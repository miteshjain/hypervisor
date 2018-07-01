
(in-package "ACL2S")

(include-book  "vamp")


(defconst *NG* 1)
;; (defconst *GUEST_MAX_PPX* 2131232)
;; (defconst *GUEST_MAX_VPX* 2343243)

(defdata guest (record (id . nat);guest identifier unique for each guest
                       (pcb . proc)
;partition memory for each guest, gmo is the starting physical page address
;note that this is not the physical page index as in the paper
                       (gmo . p-addr)
;partition the page tables for each guest, hpto is the starting
;physical address (not the index) of the host page table of
;guest. similar for spto.
                       (hpto . p-addr)
                       (spto . p-addr)
                       (max-ppx . pi)
                       (max-vpx . pi)))

(defdata guest-list (listof guest))

(defdata hypervisor (record (ng . nat)
                            (gsts . guest-list)
                            (cg .  guest)));dependent type cg \in gsts
(defun ptea-vpx (pto vpx)
  "given vpx, index of a page table entry (index is extracted from
   virtual address),return the physical address of the page table
   entry in the table"
  (a+ pto vpx))

;observers for hpt and spt page tables
;ppx(pi) * guest * mem -> pte
(defun hpt-entry (i gst mem)
  "get the ith hpt entry of gst"
  (let ((hpto (g :hpto gst)))
    (g (a+ hpto i) mem))) 

;ppx(pi) * pte * guest * mem -> mem
(defun update-hpt-entry (i hpte gst mem)
  "set the ith hpt entry of gst"
  (let ((hpto (g :hpto gst)))
    (s (a+ hpto i) hpte mem)))

;ppx(pi) * guest * mem -> pte
(defun spt-entry (i gst mem)
  "get the ith spt entry of gst"
  (let ((spto (g :spto gst)))
    (g (a+ spto i) mem)))

;ppx(pi) * pte * guest * mem -> mem
(defun update-spt-entry (i spte gst mem)
  "set the ith spt entry of gst"
  (let ((spto (g :spto gst)))
    (s (a+ spto i) spte mem)))

;ppx(pi) * guest * mem -> pte
;; guest page table is 
(defun gpt-entry (i gst mem)
  "get the ith gpt entry of gst"
  (let* ((pto (g (V_SPR_PTO) (g :spr (g :pcb gst))))
        ;; Should I be translating this physical address to real
        ;; physical using host page table ?? The answer is Yes. The
        ;; below "simplification" works in the model (vcc) because we
        ;; maintain the invariant that phsysical address x in guest
        ;; memory is mapped by hpt to physical address gmo + x

        ;; add gmo to pto since the guest memory starts form physical
        ;; address gmo in mem
        (gmo (guest-gmo gst))
        (ppto (idx+ gmo (PX pto)))) ;; since pto is a p-addr assumeed to have offset to be 0
    (g (ptea-vpx ppto i) mem)))

;ppx(pi) * pte * guest * mem -> pte
(defun update-gpt-entry (i pte gst mem)
  "set the ith gpt entry of gst"
  (let* ((pto (g (V_SPR_PTO) (g :spr (g :pcb gst))))
        (gmo (g :gmo gst))
        (ppto (a+ gmo pto)))
    (s (ptea-vpx ppto i) pte mem)))

(set-verify-guards-eagerness 0)

(defconst *ERRORPTEA* (pte *INVALID* *NOTPROT* (cons 0 0)))

(defun bus-errorp (ptea max-ppx)
  (declare (xargs :guard (and (p-addrp ptea) (natp max-ppx))))
  (<= (PX ptea) max-ppx))

;; (defun gpte-ppage-addr (pte)
;;   (pte-ppage-addr pte))
;; (defun hpte-ppage-addr (pte)
;;   (pte-ppage-addr pte))

;nat * guest * mem -> mem
(defun sync-spt-entry (i gst mem)
  "update the ith entry in spt of gst"
  (declare (xargs :guard (and (guestp gst)
                              (dmemp mem)
                              (natp i)
                              (<= i (g :max-vpx gst)))))
  (b* ((pcb (g :pcb gst))
       (spr (g :spr pcb))
       (max-ppx (g :max-ppx gst))
       (gptea (ptea-vpx (g (V_SPR_PTO) spr) i))
       ((unless (bus-errorp gptea max-ppx))
        ;;bus error ;invalid page entry
        (update-spt-entry i *ERRORPTEA* gst mem))
       (gpte (gpt-entry i gst mem))
       ((unless (not (NULL gpte)))
        (er hard 'sync-spt-entry "nil gpte-entry ~x0 in guest" i))
       (gppa (pte-ppage-addr gpte))
       ((unless (<= (PX gppa) max-ppx))
;Caught BUG, cant compare addresses with indexes
        ;;o.w bus error, so give invalid spt entry
        (er hard 'sync-spt-entry "bus error guest-physical
        address (~x0) greater than max-ppx (~x1)" gppa max-ppx))
       ;(update-spt-entry i *ERRORPTEA* gst mem))
;construct new SPTE from host PTE for the guest physical page index gppa
       (hpte (hpt-entry (PX gppa) gst mem))
; host page-table entry for the guest-physical page index must be
; always valid if the index < max-ppx (that is no bus-error above)
       ((unless (g :valid hpte))
        (er hard 'sync-spt-entry "invalid hpte at guest physical idx ~x0 entry ~x1" gppa hpte))
       ;;(update-spt-entry i *ERRORPTEA* gst mem))
       (hpte-protection (g :protection hpte))
       (hppa (pte-ppage-addr hpte))
; PX(hpt[guest physical page index]) = gmo + guest physical page index
; i.e the host physical address to which the guest physical address is
; mapped in the guest page table should be just an offset by gmo as a
; result of virtualization.
       ((unless (equal hppa (idx+ (g :gmo gst) (PX gppa))))
        ;;(update-spt-entry i *ERRORPTEA* gst mem))
          (er hard 'sync-spt-entry "page gmo + x != hpt[x]: gmo = ~x0
          gppa-index = ~x1 hppa-index = ~x3 "
              (g :gmo gst) (PX gppa) (PX hppa)))
       (gpte-valid (g :valid gpte))
       (gpte-protection (g :protection gpte))
;if gpte is valid then spte is valid
;if hpte or gpte is protected then spte is protected
       (spte-valid gpte-valid)
       (spte-protection (or hpte-protection gpte-protection))
;concatenation of gpte and hpte
       (spte (pte spte-valid spte-protection hppa)))
    (update-spt-entry i spte gst mem)))
           

;guest * nat * nat * mem -> mem
(defun sync-spt (gst j len mem)
  "update [j:j+len] entries in gst spt table"
  (declare (xargs :guard (and (guestp gst)
                              (dmemp mem)
                              (natp j)
                              (natp len))))
  (if (zp len)
      (sync-spt-entry j gst mem)
    (sync-spt gst (1+ j) (1- len) (sync-spt-entry j gst mem))))

;p-addr * p-addr * nat * mem -> mem
(defun init-hpt-loop (hpa gm-pa len mem)
  "initialize all entries of hpt table in mem starting from hpa for len entries
  hpt maps injectively into guest memory portion(gm-pa)"
  (declare (xargs :guard (and (dmemp mem)
                              (natp len)
                              (p-addrp gm-pa)
                              (p-addrp hpa))))
  (if (zp len)
    mem
    (init-hpt-loop (a+ hpa 1) (idx+ gm-pa 1) (1- len)
                   (s hpa (pte *VALID* *NOTPROT* gm-pa) mem))))


;guest * mem -> mem
(defun init-hpt (gst mem)
  "initialize the hpt page table of gst in mem"
  (declare (xargs :guard (and (guestp gst)
                              (dmemp mem))))
  (b* ((hpto (g :hpto gst))
        (gmo (g :gmo gst))
        (max-ppx (g :max-ppx gst))
        ;; crude check if hpt and gm should be disjoint in mem
        ;; assumes hpt is place after the guest memory
        ((unless (> (px hpto) (px (idx+ gmo max-ppx))))
         (er hard 'init-hpt "hpt and gm not disjoint hpto=~x0 gm-end=~x1" hpto (idx+ gmo max-ppx))))
    (init-hpt-loop (a+ hpto 1) (idx+ gmo 1) max-ppx 
; the first entry in the hpt points to the start of the guest memory
; (gmo) and this should be protected so that any future change to the
; origin is captured
                   (s hpto (pte *VALID* *PROT* gmo) mem))))


;; (defun pair-wise-disojint (gmo hpto spto max-ppx max-vpx)
;;   (let* ((gm-end (idx+ gmo max-ppx))
;;          (hpt-end (idx+ hpto max-ppx))
;;          (spt-end (idx+ spto max-vpx)))
;;     ;; hpt does not overlap with gm
;;   (and (not (and (>= hpto gmo)
;;                  (<= hpto gm-end)))
;;        (not (and (>= hpt-end gmo)
;;                  (<= hpt-end gm-end)))
;;        ;; hpt does not overlap with spt
;;        (not (and (>= hpto spto)
;;                  (<= hpto spt-end)))
;;        (not (and (>= hpt-end spto)
;;                  (<= hpt-end spt-end)))
;;        ;; spt does not overlap with gm
;;        (not (and (>= spto gmo)
;;                  (<= spto gm-end)))
;;        (not (and (>= spt-end gmo)
;;                  (<= spt-end gm-end))))))
       
;; ;guest * mem -> mem
;; (defun init-hpt-and-spt (gst mem)
;;   "initialize the spt and hpt data structures of a guest gst in mem"
;;   (declare (xargs :guard (and (guestp gst)
;;                               (dmemp mem))))
;; ;NOTE: g->pcb is an initial_proc() with 0 for PTO and PTL
;;   (let* ((gmo (g :gmo gst))
;;          (spto (g :spto gst))
;;          (hpto (g :spto gst))
;;          (max-vpx (g :max-vpx gst))
;;          (max-ppx (g :max-ppx gst)))
;;     ;; the following three memory regions should be pairwise disjoint
;;     ;; 1) mem[gmo : gmo + max-ppx], 2) mem[hpto: htpo + max-ppx], 3)
;;     ;; mem[spto: spto + max-vpx]
;;     (if (pair-wise-disojint gmo hpto spto max-ppx max-vpx)
;;         (sync-spt gst 0 0 (init-hpt gst mem))
;;       mem)))

;guest * mem -> mem
(defun init-hpt-and-spt (gst mem)
  "initialize the spt and hpt data structures of a guest gst in mem"
  (declare (xargs :guard (and (guestp gst)
                              (dmemp mem))))
;NOTE: g->pcb is an initial_proc() with 0 for PTO and PTL
  (sync-spt gst 0 0 (init-hpt gst mem)))

;Note the signature, its ppa not ppx
;p-addr * p-addr * nat * mem * boolean -> mem
(defun update-hpt-entries-with-prot-bit (hpa len mem prot-set)
  "update protection bit of page-table entries in hpt in mem starting
   from hpa for len entries, if prot-set is true then set the
   protection bit"
  (declare (xargs :guard (and (dmemp mem)
                              (natp len)
                              (booleanp prot-set)
                              (p-addrp hpa))))
  (if (zp len)
    mem
    (update-hpt-entries-with-prot-bit (a+ hpa 1) (1- len)
;ASK - I am just updating memory, not hpt table. and hpa passed is gpto !!
       (s hpa (s :protection prot-set (g hpa mem)) mem)
       prot-set)))

;NOTE: we store as pto the complete physical address, not a page index. We must
;make sure this fact is used consistently.
;p-addr * guest * mem-> gst * mem
(defun handle-movi2pto (new gst mem)
  "write new pto to spr[PTO] of pcb of gst and 
   also do relevant update hpt/spt in mem"
  (declare (xargs :guard (and (guestp gst)
                              (dmemp mem)
                              (p-addrp new))))

  (let* ((spr (g :spr (g :pcb gst)))
         (gpto (g (V_SPR_PTO) spr))
         (gptl (g (V_SPR_PTL) spr))
         ;; ptl is a natural number indicating the length of the page
         ;; table i.e the page table is located in location gm[pto]
         ;; through gm[(a+ pto ptl)]
         (l (min (PX (a+ gpto gptl)) (guest-max-ppx gst)))
         (hpto (guest-hpto gst))
         (k (PX gpto)))
    ;; Un protect the host-page-table entries pointing (WHY??)
    (let ((mem (update-hpt-entries-with-prot-bit
                (a+ hpto k) ;; origin of hpt in mem
                (- l k)
                mem *NOTPROT*))
          (l (min (PX (a+ new gptl))  (guest-max-ppx gst)))
          (k (PX new))) ;; assume that the new gpto is page aligned i.e (WA new) = 0
    ;;  protect the all the entries in the new host page table so that
    ;; any subsequent update (movi2s with address corresponding to the
    ;; new guest page table entries) to the guest page table by the
    ;; guest results in an interrupt and the hypervisor can update the
      ;; hpt and spt and keep it in sync.
      (let ((new-gst (s :pcb
                        (increment-pcs (s :spr (s (V_SPR_PTO) new spr)
                                          (g :pcb gst))) gst)))
        (mv new-gst
          (sync-spt new-gst 0 gptl 
                    (update-hpt-entries-with-prot-bit (a+ hpto k)
                                                      (- l k) mem *PROT*)))))))


;nat * guest * mem-> gst * mem
(defun handle-movi2ptl (new gst mem)
  "write new ptl to spr[PTL] of pcb of gst and 
   also do relevant update hpt/spt in mem"
  (declare (xargs :guard (and (guestp gst)
                              (dmemp mem)
                              (natp new))))
  (let* ((new (min new (g :max-vpx gst)))
         (spr (g :spr (g :pcb gst)))
         (gpto (g (V_SPR_PTO) spr))
         (gptl (g (V_SPR_PTL) spr))
         (hpto (guest-hpto gst)))
    (if (> new gptl)
        (let ((l (min (PX (a+ gpto new)) (guest-max-ppx gst)))
              (k (min (PX (a+ gpto gptl)) (guest-max-ppx gst))))
          (let ((new-gst (s :pcb (increment-pcs (s :spr 
                                      (s (V_SPR_PTL) new spr)
                                      (g :pcb gst))) gst)));update ptl spr in pcb of guest
            (mv new-gst (sync-spt new-gst 0 new 
                                  (update-hpt-entries-with-prot-bit
                                   (a+ hpto (+ k 1)) (- l k)  mem *PROT*)))))
      ;; else new < gptl and update gpte therefore shrink the spt and
      ;; updated the hpt to mark unused pte as not write-protected
      (let ((l (min (PX (a+ gpto gptl)) (guest-max-ppx gst)))
            (k (min (PX (a+ gpto new)) (guest-max-ppx gst))))
        (mv (s :pcb (increment-pcs (s :spr 
                                      (s (V_SPR_PTL) new spr)
                                      (g :pcb gst))) gst);update ptl spr in pcb of guest
            (update-hpt-entries-with-prot-bit
             (a+ hpto (+ k 1)) (- l k) mem *NOTPROT*))))))


;nat * nat * all -> gpr
(defun init-gpr (i n val)
  "initialize n registers with 0"
  (if (zp n)
    nil
    (cons (cons i val)
          (init-gpr (1+ i) (1- n) val))))
;-> spr
(defun init-spr ()
  (list (cons (V_SPR_SR) 0)
        (cons (V_SPR_ESR) 0)
        (cons (V_SPR_ECA) 'V_IL_NONE)
        (cons (V_SPR_EPC) (cons 0 0))
        (cons (V_SPR_EDPC) (cons 0 0))
        (cons (V_SPR_EDATA) 0) 
        (cons (V_SPR_PTO) (cons 0 0))
;physical page address in mem of page table (unlike in paper)
        (cons (V_SPR_PTL) 0);len of page table
        (cons (V_SPR_EMODE) 0);either 0(sys mode) or 1(user mode)
        (cons (V_SPR_MODE) 0)))

;corresponds to reset-guest
;nat * nat * nat * p-addr -> guest
(defun init-guest (id max-ppx max-vpx gmo)
  "partially initialize a guest partition data structure"
  (guest id
         (exec-jisr (proc (V_SISR)
                          (a+ (V_SISR) 1)
                          (init-gpr 0 (V_GPR_NUM) 0)
;init all regs with 0 content
                          (init-spr)
                          nil)
                    'V_IL_RESET)
         ;;gmo
         gmo 
         ;;htpo
         (a+ gmo (* (1+ max-ppx) *PG_SZ*))
         ;;spto = htpo + max-ppx ( number of entries in hpt) + 1
         (a+ gmo (+ (* (1+ max-ppx) *PG_SZ*) (1+ max-ppx)))
         ;;instruction memory
         ;;nil
         max-ppx
         max-vpx))

;; The partitino of a guest partition starting at gmo
(defun guest-partition-mem-size (mppx mvpx)
  (+  (* (1+ mppx) *PG_SZ*);guest mem size
      (1+ mppx)  ;hpt table size
      (1+ mvpx))) ;spt table size

;nat * nat * nat * nat * nat -> guest-list
(defun init-guests (i ng gmo max-ppx max-vpx)
  "initialize ng guests, gmo is the memory offset of guest i in
memory"
  (if (zp ng)
    nil
    (let ((gst (init-guest i max-ppx max-vpx gmo)))
      (cons gst 
            (init-guests (1+ i) (1- ng) 
                         (a+ gmo (guest-partition-mem-size max-ppx max-vpx))
                         max-ppx max-vpx)))))

;guest-list * mem -> mem
(defun init-guest-mem-pagetables (gst-lst mem)
  "init the memory and page tables of all guests"
  (if (endp gst-lst)
    mem
    (init-guest-mem-pagetables (cdr gst-lst) 
                               (init-hpt-and-spt (car gst-lst) mem))))

;nat * nat * nat * mem -> hypervisor * mem
(defun handle-reset (ng max-ppx max-vpx mem)
  "initializes the hypervisor data structures and the guest mem/pagetables"
  (declare (xargs :guard (and (natp ng) (natp max-vpx) (natp max-ppx))))
  (let* ((gsts (init-guests 0 ng 0 max-ppx max-vpx));boot time, write from 0
         (mem (init-guest-mem-pagetables gsts mem)))

    (mv (hypervisor ng gsts (car gsts)) mem)))

;inst * guest * mem -> il * guest * mem
(defun emulate-privileged-operation (I gst mem)
  (declare (xargs :guard (and (guestp gst)
                              (dmemp mem)
                              (instp I))))
  (let ((opcode (g :op I))
        (pcb (g :pcb gst)))
    (case opcode
      (rfe (mv-let (gil p)
                   (exec-rfe pcb)
                   (mv gil (s :pcb p gst) mem)))
      (movs2i (mv-let (gil p)
                      (exec-movs2i I pcb)
                      (mv gil (s :pcb p gst) mem)))
      (movi2s 
        (if (and (sys-mode? pcb)
                 (or (equal (g :sa I) (V_SPR_PTO))
                     (equal (g :sa I) (V_SPR_PTL))))
            (let* ((rd (g :rd I))
                   (gpr (g :gpr pcb))
                   (rd-val (g rd gpr)))
              (mv-let (gst mem)
                      (if (equal (g :sa I) (V_SPR_PTO))
                          (handle-movi2pto rd-val gst mem) 
                          (handle-movi2ptl rd-val gst mem))
                      (mv 'V_IL_NONE gst mem)))
            (mv-let (gil p)
                    (exec-movi2s I pcb)
                    (mv gil (s :pcb p gst) mem))))
      (otherwise (mv 'V_IL_ILLEGAL gst mem)))))


(defun get-guest-by-id-helper (id gsts)
  (if (endp gsts)
    (er hard 'get-guest-by-id-helper "~x0 guest id not found~%" id)
;not found (Possible bug in calling context)
    (if (= id (g :id (car gsts)))
      (car gsts)
      (get-guest-by-id-helper id (cdr gsts)))))

;  nat * hypervisor -> guest
(defun get-guest-by-id (id hvr)
  "get guest whose id is id"
  (get-guest-by-id-helper id (g :gsts hvr))) 

#|
(defun  update-guest (gst hvr)
  "update guest in hypervisor hvr"
  (if (= (g :id gst) (g :id (g :cg hvr)))
    (up hvr :cg gst;update  current guest field
           ;;then update the guest with same id in gst list
           ;;id is one-indexed, whereas, list indexing is zero-indexed
           :gsts (update-nth (1- (g :id gst)) gst (g :gsts hvr)))
    (up hvr 
          ;;then update the guest with same id in gst list
          ;;id is one-indexed, whereas, list indexing is zero-indexed
          :gsts (update-nth (1- (g :id gst)) gst (g :gsts hvr)))))
|#

;gst * gsts -> gsts
(defun  update-current-guest-in-gsts (cgst gsts)
  "update current guest in guest list gsts"
  (cond ((endp gsts)
         nil)
        ((equal (g :id cgst) (g :id (car gsts)))
         (cons cgst (cdr gsts)))
        (t (cons (car gsts) (update-current-guest-in-gsts cgst (cdr gsts))))))

(defun  update-current-guest (cgst hvr)
  "update current guest and gsts in hypervisor hvr"
  (if (= (g :id cgst) (g :id (g :cg hvr)))
    (up hvr :cg cgst;update current guest field
           ;;then update the guest with same id in gst list
           ;;id is one-indexed, whereas, list indexing is zero-indexed
           :gsts (update-current-guest-in-gsts cgst (g :gsts hvr)))
    (prog2$
     (er hard 'update-current-guest "Updating a guest which is not the current guest!!")
     hvr)))

;inst * hypervisor * mem-> hypervisor * mem
(defun handle-illegal (I hvr mem)
  "hvr emulates a privileged operation"
  (mv-let (gil gst mem)
          (emulate-privileged-operation I (g :cg hvr) mem)
          (if (not (equal gil 'V_IL_NONE))
              (mv (update-current-guest 
                   (s :pcb (exec-jisr (g :pcb gst) gil) gst) hvr)
                  mem)
            (mv (update-current-guest gst hvr) 
                mem))))

(defun update-mem (a data mem)
  (declare (xargs :guard (and (p-addrp a)
                              (datap data)
                              (dmemp mem))))
  (s a data mem))

;guest * (oneof p-addr v-addr) * boolean * data * mem -> boolean * guest * mem
(defun handle-pf (gst a store? data mem)
  "handle pf, if done, return true, o.w false, and 
   the caller then takes care of it"
  (declare (xargs :guard (and (guestp gst)
                              (or (v-addrp a) (p-addrp a))
                              (booleanp store?)
                              (dmemp mem)
                              ;;data can be nat,v-addr,pte, p-addr??
                              (datap data))))

  ;; Check whether the page fault was triggered by an attempted update of the
  ;; guest page table. If no, return 'false' to let the caller inject the
  ;; page fault into the guest. If yes, simulate the attempted update for the
  ;; guest (and update the shadow page tables for the updated guest PTE).
  (let* ((pcb (g :pcb gst))
         (spr (g :spr pcb))
         (gpto (g (V_SPR_PTO) spr))
         (gmo (g :gmo gst))
         (gptl (g (V_SPR_PTL) spr))
         (usr? (not (sys-mode? pcb)))
         (px (PX a))
         (max-len (if usr? gptl (g :max-ppx gst))))
    ;; store word instruction
    (if (and store? (<= px max-len))
        (if usr?
            (let* ((vpx px) ;; a is a virtual address
                   (gpte (gpt-entry vpx gst mem)))
              (cond ((> (PX (ptea-vpx gpto vpx)) (g :max-ppx gst))
                     ;;page table entry address outside gst phys mem
                     (mv nil gst mem))
                    ((or (not (g :valid gpte))
                          (g :protection gpte)
                          (> (PX (g :ppage-addr gpte)) (g :max-ppx gst)))
                     ;; This is the case when the page is not valid or
                     ;; is write-protected (as given by shadow page
                     ;; table entry we are here because store-word
                     ;; instruction ended up in PF using SPT). Inspect
                     ;; if the page as given by the original guest
                     ;; page table also says the same and if they both
                     ;; agree it indicates a true page fault and
                     ;; should be handled by the guest. BOZO: In what
                     ;; case the spt and gpt will not agree on page
                     ;; attributes ?????
                     (mv nil gst mem))
                    (t
                     ;; case when gpte and spte do not agree on the
                     ;; attributes of the page i.e the gpte says that
                     ;; the page is either valid or not write
                     ;; protected. In this case then update the memory
                     ;; with the store-word and also update the spt
                     ;; entry (sync-spt-enrty function takes care of
                     ;; syncing the attributes as well).

                     ;;Note that we are syncing the spt entry even in
                     ;;case the write is to update a page table entry
                     ;;in guest page table i.e pto <= pa <= pto + ptl
                     ;;BOZO: I am not sure if we should update a gpte
                     ;;in usr-mode ?
                     (let* ((ppx (PX (pte-ppage-addr gpte)))
                            (ppx-in-hvr (+ (PX gmo) ppx))
                            (hpa (cons ppx-in-hvr (WX a)))
                            (mem-store (update-mem hpa data mem))
                            (spt-mem (sync-spt-entry vpx gst mem-store)))
                       (mv t (s :pcb (increment-pcs pcb) gst) spt-mem)))))
          ;; In system mode, a page fault is truely because of the
          ;; guest.The host processor uses HPT for translation. In
          ;; this case PFLS is generated, if the guest physical
          ;; address is greater than max-ppx (in which case we do not
          ;; expect a hpte to exist). In this case just pass on the PF
          ;; to the guest OS. 2) host page-table entry is not valid or
          ;; is write-protected. Since in system mode guest should be
          ;; able to write to any page unless it is write protected
          ;; (ie hpte should always be valid for any guest physical
          ;; address in range). Thus its only that hpte has write
          ;; protected the page. However, the only entry that is write
          ;; protected is the first entry which points to the
          ;; partition of the memory for the guest. So in either case
          ;; we should just pass on the fault for the OS to handle.
          (mv nil gst mem))
      (mv nil gst mem))))



;; ;guest -> inst
;; (defun fetch-PFLS/ILLEGAL-causing-instr (gst mem)
;;   "Fetch the instruction that threw the PFLS or ILLEGAL"
;;     (let* ((pcb (g :pcb gst))
;;            (a (g :dpc pcb)))
;;       (mv-let (ef addr)
;;               (va-to-pa a pcb mem nil)
;;               (declare (ignore ef))
;;               (g addr mem))))


(defun fetch-PFLS/ILLEGAL-causing-instr (gst)
  "Use the delay-pc to fetch the instruction that threw the PFLS or
ILLEGAL"
  (let* ((pcb (g :pcb gst))
         (a (g :dpc pcb))
         (imem (proc-instmem pcb)))
    (g a imem)))

;il * instr * hypervisor * mem -> hypervisor * mem
(defun hv-dispatch (eca edata hvr mem)
  "hypervisor dispatch code"
  (declare (xargs :guard (and (hypervisorp hvr)
                              (ilp eca)
                              (dmemp mem)
                              )))
    (case eca
      ;; (V_IL_RESET
      ;;  (handle-reset *NG* *MAX_PPX* *MAX_VPX*  mem))
      (V_IL_PFF
       ;;Page faults on fetch are accurate, always inject BOZO: in the
       ;;current model instruction fetch does not go through va-to-pa
       ;;translation and therefore never page faults. Leaving the code
       ;;here for later
       (let* ((cg (g :cg hvr))
              (pcb (g :pcb cg))
              (spr (g :spr pcb)))
         (mv (update-current-guest 
              (s :pcb
                 (exec-jisr 
                  (s :spr (s (V_SPR_EDATA) (g :dpc pcb) spr) pcb)
                  'V_IL_PFF) cg)
              hvr)
             mem)))
      (V_IL_ILLEGAL
       (handle-illegal (fetch-PFLS/ILLEGAL-causing-instr
                        (g :cg hvr)) hvr mem))
      (V_IL_PFLS
       (b* ((cg (g :cg hvr))
            (I (fetch-PFLS/ILLEGAL-causing-instr cg))
            (pcb (g :pcb cg))
            (va (immI-vaddr I pcb))
            ((mv handled? new-cg mem)
             (handle-pf cg
                        va
                        (equal (g :op I) 'sw)
                        (g (g :rd I) (g :gpr pcb))
                        mem))
            (pcb (g :pcb new-cg))
            (spr (g :spr pcb)))
         (if (not handled?);pass on the buck
             (mv (update-current-guest 
                  (s :pcb (exec-jisr (s :spr (s (V_SPR_EDATA) va spr) pcb) 
                                     'V_IL_PFLS)
                     new-cg) 
                  hvr)
                 mem)
           (mv (update-current-guest new-cg hvr) mem))))
      (V_IL_TRAP
        (let* ((cg (g :cg hvr));suspended guest
               (pcb (g :pcb cg));suspended partition control block
               (spr (g :spr pcb)));its spr contents
          ;;NOTE: pcs of current guest have already been incremented
          (if (sys-mode? pcb);if in sys mode, do yield
            (mv (s :cg 
                   (get-guest-by-id (mod  (1+ (g :id cg)) (g :ng hvr)) hvr)
                   hvr);yield to next guest
                mem)
            ;;o.w. do normal trap emulation
            (let* ((spr (s (V_SPR_EDATA) edata spr));update spr
                   (pcb (s :spr spr pcb)));update pcb
              (mv (update-current-guest 
                   (s :pcb (exec-jisr pcb 'V_IL_TRAP) cg) hvr) mem)))))
      (otherwise (mv hvr mem))))#|ACL2s-ToDo-Line|#

