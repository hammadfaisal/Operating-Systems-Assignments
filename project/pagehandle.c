#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "spinlock.h"
#include "x86.h"
#include "proc.h"
#include "elf.h"

#define SWAPSLOTSIZE 8
#define SWAPSTART 2

struct {
    int page_perm;
    int is_free;
    unsigned long long ref_procs;
    struct spinlock lock;
} swap_slots[SWAPBLOCKS/SWAPSLOTSIZE];

struct {
    unsigned long long ref_procs;
    unsigned int vaddr;
    struct spinlock lock;
} rmap[PHYSTOP/PGSIZE];


void unset_access_bit(uint padd) {
    acquire(&rmap[padd/PGSIZE].lock);
    uint va = rmap[padd/PGSIZE].vaddr;
    for (uint j = 0; j< NPROC;j++) {
        if ((rmap[padd/PGSIZE].ref_procs >> j) & 1LL) {
            struct proc *cp = get_proc(j);
            uint* pte = walkpgdir(cp->pgdir, (void *)va, 0);
            *pte &= ~PTE_A;
            if (j == get_proc_table_ind(myproc()->pid)) {
                lcr3(V2P(myproc()->pgdir));
            }
        }
    }
    release(&rmap[padd/PGSIZE].lock);
}

void free_swap_slot(int blockno, int ptable_ind) {
    if (ptable_ind < 0 || ptable_ind >= NPROC) {
        panic("free_swap_slot: invalid ptable_ind");
    }
    int slotno = (blockno-SWAPSTART)/SWAPSLOTSIZE;
    acquire(&swap_slots[slotno].lock);  
    swap_slots[slotno].ref_procs &= ~(1LL << ptable_ind);
    if (swap_slots[slotno].ref_procs == 0) {
        swap_slots[slotno].is_free = 1;
    }
    release(&swap_slots[slotno].lock);
}

void pginit(void) {
    int i;
    for (i = 0; i < SWAPBLOCKS/SWAPSLOTSIZE; i++) {
        swap_slots[i].is_free = 1;
        initlock(&swap_slots[i].lock, "swaplock");
    }
    for (i = 0; i < PHYSTOP/PGSIZE; i++) {
        initlock(&rmap[i].lock, "rmaplock");
    }
}

void add_rmap_proc(unsigned int padd, int ptable_ind) {
    acquire(&rmap[padd/PGSIZE].lock);
    rmap[padd/PGSIZE].ref_procs |= (1LL << ptable_ind);
    release(&rmap[padd/PGSIZE].lock);
}

void remove_rmap_proc(unsigned int padd, int ptable_ind) {
    acquire(&rmap[padd/PGSIZE].lock);
    rmap[padd/PGSIZE].ref_procs &= ~(1LL << ptable_ind);
    release(&rmap[padd/PGSIZE].lock);
}

void change_rmap_vaddr(unsigned int padd, unsigned int vaddr) {
    acquire(&rmap[padd/PGSIZE].lock);
    rmap[padd/PGSIZE].vaddr = vaddr;
    release(&rmap[padd/PGSIZE].lock);
}

int count_refs(unsigned int padd) {
    unsigned long long n = rmap[padd/PGSIZE].ref_procs;
    int count = 0;
    while (n) {
        n &= (n - 1);
        count++;
    }
    return count;
}

int swap_out_page() {
    struct proc *v_proc = victim_proc();
    int vpg = victim_page(v_proc);
    if (vpg <0) {
        convert_acc_pg(v_proc);
        vpg = victim_page(v_proc);
    }
    if (vpg < 0)
        panic("swap_page_out: no victim page");
    uint *curpte = walkpgdir(v_proc->pgdir, (void *)vpg, 0);
    uint padd = PTE_ADDR(*curpte);
    acquire(&rmap[padd/PGSIZE].lock);
    if (rmap[padd/PGSIZE].ref_procs == 0) {
        release(&rmap[padd/PGSIZE].lock);
        return 0; // page is already swapped out
    }
    int current_proc_ind = get_proc_table_ind(myproc()->pid);
    int i;
    for (i = 0; i < SWAPBLOCKS/SWAPSLOTSIZE; i++) {
        acquire(&swap_slots[i].lock);
        if (swap_slots[i].is_free) {
            swap_slots[i].is_free = 0;
            swap_slots[i].page_perm = *curpte & 0xFFF;
            swap_slots[i].ref_procs = rmap[PTE_ADDR(*curpte)/PGSIZE].ref_procs;
            release(&swap_slots[i].lock);

            int new_pte = ((i*SWAPSLOTSIZE + SWAPSTART)<<12) | PTE_SW;
            for (uint j = 0; j< NPROC;j++) {
                if ((rmap[padd/PGSIZE].ref_procs >> j) & 1LL) {
                    struct proc *cp = get_proc(j);
                    uint* pte = walkpgdir(cp->pgdir, (void *)vpg, 0);
                    cp->rss -= PGSIZE;
                    *pte = new_pte;
                    if (j == current_proc_ind) {
                        lcr3(V2P(myproc()->pgdir));
                    }
                    // cprintf("swapping out page %x for process %d\n", vpg, cp->pid);
                }
            }
            rmap[padd/PGSIZE].ref_procs = 0;
            release(&rmap[padd/PGSIZE].lock);
            write_page_to_disk((char *)P2V(padd), i*SWAPSLOTSIZE + SWAPSTART);
            kfree((char *)P2V(padd));
            return 0;
        }
        release(&swap_slots[i].lock);
    }
    release(&rmap[padd/PGSIZE].lock);
    return -1;
}

// swap in page
void handle_page_present(uint va, pte_t *pte) {
    struct proc *p = myproc();
    int ptable_ind = get_proc_table_ind(p->pid);
    
    int blockno = PTE_ADDR(*pte)/PGSIZE;
    int slotno = (blockno-SWAPSTART)/SWAPSLOTSIZE;
    if (!(*pte & PTE_SW) || swap_slots[slotno].is_free || ((swap_slots[slotno].ref_procs & (1LL << ptable_ind)) == 0)) {
        panic("handle_page_present: page not swapped out");
    }
    
    char* mem = kalloc();
    if (mem == 0) {
        panic("handle_page_present: kalloc");
    }
    read_page_from_disk(mem, blockno);
    acquire(&swap_slots[slotno].lock);
    if (swap_slots[slotno].is_free) {
        release(&swap_slots[slotno].lock);
        kfree(mem);
        return;
    }
    int new_pte = V2P(mem) | swap_slots[slotno].page_perm;
    for (uint j = 0; j< NPROC;j++) {
        if ((swap_slots[slotno].ref_procs >> j) & 1LL) {
            struct proc *cp = get_proc(j);
            uint* pte = walkpgdir(cp->pgdir, (void *)va, 0);
            cp->rss += PGSIZE;
            *pte = new_pte;
            if (j == ptable_ind) {
                lcr3(V2P(p->pgdir));
            }
        }
    }
    int ref_procs = swap_slots[slotno].ref_procs;
    swap_slots[slotno].is_free = 1;    
    release(&swap_slots[slotno].lock);

    acquire(&rmap[PTE_ADDR(new_pte)/PGSIZE].lock);
    rmap[PTE_ADDR(new_pte)/PGSIZE].ref_procs = ref_procs;
    rmap[PTE_ADDR(new_pte)/PGSIZE].vaddr = va;
    release(&rmap[PTE_ADDR(new_pte)/PGSIZE].lock);
}
    

void handle_write_page(uint va, pte_t *pte) {
    uint padd = PTE_ADDR(*pte);
    int refs = count_refs(padd);
    struct proc *p = myproc();
    int ptable_ind = get_proc_table_ind(p->pid);
    if (refs == 1) {
        *pte |= PTE_W;
    }
    else {
        char* mem = kalloc();
        if (mem == 0) {
            panic("handle_write_page: kalloc");
        }
        remove_rmap_proc(padd, ptable_ind);
        *pte = V2P(mem) | PTE_W | PTE_U | PTE_P;
        memmove(mem, (char *)P2V(padd), PGSIZE);
        add_rmap_proc(V2P(mem), ptable_ind);
        change_rmap_vaddr(V2P(mem), va);
    }
    lcr3(V2P(p->pgdir));
}




void handle_page_fault() {
    uint va = PGROUNDDOWN(rcr2());
    pte_t *pte = walkpgdir(myproc()->pgdir, (void *)va, 0);
    if (!(*pte & PTE_P)) {
        handle_page_present(va, pte);
        return;
    }
    if (!(*pte & PTE_W)) {
        if (!(*pte & PTE_U)) {
            panic("handle_page_fault: page not writable");
        }
        handle_write_page(va, pte);
        return;
    }
    panic("handle_page_fault");
}