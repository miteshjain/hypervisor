(in-package "ACL2S")

(defun up-macro (pairs ans)
  (if (endp pairs)
      ans
    (up-macro (cddr pairs) `(s ,(car pairs)
                               ,(cadr pairs)
                               ,ans))))
(defmacro up (st &rest pairs)
  "do the update in the sequence of pairs"
  (up-macro pairs st))
;Data definitions


(defconst *PG_SZ* 4)
(defconst *MAX_PPX* 31)
(defconst *MAX_VPX* 15)

;index in a page table or any memory
(defdata pi (range integer (0 <= _ <= (* 10 *MAX_PPX*))))
;virtual page index (bound this)
;; bumping up the max-page index because we use the same data
;; structure for the hypervisor
(defdata vpi (range integer (0 <= _ <= (* 10 *MAX_VPX*))))

(defdata offset (range integer (0 <= _ <= (1- *PG_SZ*)))); use range defdata to constrain the range


;physical address
(defdata p-addr (cons pi offset))
;virtual address 
(defdata v-addr (cons vpi offset))
;page table entry
(defdata pte (record (valid . boolean);is this page valid
                     (protection . boolean);is this page write-protected
;physical address of page this pte points to
                     (ppage-addr . p-addr)))

(defconst *VALID* t)
(defconst *INVALID* nil)
(defconst *PROT* t)
(defconst *NOTPROT* nil)

;(defdata page-table (listof (cons p-addr pte)));p-addr -> pte

;pc is just an index into MEM
(defdata pc-t p-addr)
(defdata dpc-t p-addr)

(defdata data (oneof nat pte v-addr p-addr))
;for now data is just nat numbers plus TODO

(defdata dmem (map p-addr data))
;memory stores both data and page table entries

;interrupt levels
(defdata IL (enum '(V_IL_NONE V_IL_RESET V_IL_PFF 
                              V_IL_ILLEGAL V_IL_PFLS V_IL_TRAP)))

;General Purpose Registers
(defdata GPRi nat)
(defdata regdata (oneof integer IL pte v-addr p-addr))
(defdata GPR-t (listof (cons GPRi regdata)))


;Instruction types
(defdata op-codeR (enum '(add sub movs2i movi2s)))
(defdata op-codeI (enum '(lw sw addi subi beqz jr)))
(defdata op-codeJ (enum '(j trap rfe nop)))
(defdata opcode (oneof op-codeJ op-codeI op-codeR))

(defdata SPRi (enum '(0 1 2 3 4 5 9 10 11 16)))

(defdata instR (record (op . op-codeR)
                       (rd . GPRi);dest
                       (rs1 . GPRi);source1
                       (rs2 . GPRi)
                       (sa . SPRi)));special purpose reg index

(defdata instI (record (op . op-codeI)
                       (rd . GPRi)
                       (rs1 . GPRi)
                       (imm . integer)))

(defdata instJ (record (op . op-codeJ)
                       (imm . integer)))

(defdata inst (oneof instI instR instJ))

;; Mitesh: not used to fetch the instruction and not part of any state
;; so why is it even there
(defdata imem (listof (cons p-addr inst)))

(defdata Cbool (oneof 0 1));C uses 0 and 1 as booleans/bits


(defdata SPR-t (list (cons 0 Cbool)
                     (cons 1 Cbool)
                     (cons 2 il)
                     (cons 3 pc-t)
                     (cons 4 pc-t)

;either imm(J instr) or instruction itself ASK
                     (cons 5 (oneof nat p-addr inst)) 

;physical page address in mem of page table (unlike in paper)
                     (cons 9 p-addr)
                     (cons 10 nat);len of page table
                     (cons 11 Cbool);either 0(sys mode) or 1(user mode)
                     (cons 16 Cbool)))


(defdata proc (record (dpc . dpc-t) 
                      (pc . pc-t)
                      (gpr . gpr-t)
                      (spr . spr-t)
                      (instmem . imem)))

(defdata mach (record (p . proc)
                      (mem . dmem)))

(defun PX (p-addr)
  (car p-addr))

(defun WX (p-addr)
  (cdr p-addr)) 

;ppx -> p-addr
(defun PA (ppx)
  "give page address of a physical page index ppx"
  (cons (* ppx *PG_SZ*) 0))

(defdata addr (oneof p-addr v-addr))

;p-addr * pi -> p-addr
(defun idx+ (pa idx)
  (declare (xargs :guard (and (addrp pa) (natp idx))
                  :verify-guards nil))
  "give the page address that is the result of incrementing
   the page index of address pa i times"
  (cons (+ (PX pa) idx) (WX pa)))



;SPecial Purpose Registers
(defun V_SPR_SR () 0) ;// status register
(defun V_SPR_ESR () 1) ;// exception status register
(defun V_SPR_ECA () 2) ;// exception cause register
(defun V_SPR_EPC () 3) ;// exception program counter
(defun V_SPR_EDPC () 4) ;// exception delayed program counter
(defun V_SPR_EDATA () 5) ;// exception data
(defun V_SPR_PTO () 9) ;// page-table origin (only lower 20 bits
;significant) Physical page index in physical memory, pto tells where
;the page table starts in memory. This is however stored as p-addr
;with index to page and offset, (offset should be zero). So the
;pysical address is (* (px pto) *PG_SZ*)
(defun V_SPR_PTL () 10) ;page-table last index (only lower 20 bits significant)
;ptl tells the number of entries in the page table 
(defun V_SPR_EMODE () 11) ;// exception mode (only lowest bit significant)
(defun V_SPR_MODE () 16) ;// mode (only lowest bit significant)

(defun V_GPR_NUM () 8) ;change later?



(defmacro USER_MODE () 1)
(defmacro SYSTEM_MODE () 0)

;get macro
(defmacro g (k r)
  `(mget ,k ,r))

;set macro
(defmacro s (k v r)
  `(mset ,k ,v ,r))

;proc -> boolean
(defun sys-mode? (p)
  "Is p in system mode, give t, else nil"
  (= (SYSTEM_MODE) (g (V_SPR_MODE) (g :spr p))))
    
;; (defun a+ (pa i)
;;   "give the address that is the result of incrementing
;;    the physical address (pa) i times"
;;   (if (zp i)
;;       pa
;;     (b* ((offset (WX pa))
;;          (px (PX pa)))
;;       (if (< (+ offset i) *PG_SZ*) ;; BOZO i is the page index to the page and offset is the word in the page 
;;           (cons px (+ i offset))
;;         (a+ (cons (+ 1 px) 0) (- i (- *PG_SZ* offset)))))))

(defun a+ (pa i)
  (let* ((off (WX pa))
         (idx (PX pa))
         (q (floor (+ off i) *PG_SZ*))
         (r (mod (+ off i) *PG_SZ*)))
    (cons (+ idx q) r)))

;; (thm (implies (and (addrp pa) (natp i) (< (WX pa) *PG_SZ*))
;;               (equal (a+ pa i) (a+-non pa i))))


;; (defun a- (pa i)
;;   "give the address that is the result of incrementing
;;    the physical address (pa) i times"
;;   (if (zp i)
;;       pa
;;     (b* ((offset (WX pa))
;;          (px (PX pa)))
;;       (if (>= offset i)
;;           (cons px (- offset i))
;;         (a- (cons (1- px) (1- *PG_SZ*)) (- i offset))))))

;address translation
;; v-addr|p-addr * proc * boolean-> (mv erp  p-addr)
(defun va-to-pa (va p mem w)
"given a address, proc, mem and a write flag, 
return the 2 tuple of error flag and translated physical address"
(let* ((vpx (PX va)) ;virtual page index
       (spr (g :spr p))                
       (mode (g (V_SPR_MODE) spr))
       (pto (g (V_SPR_PTO) spr))
       (ptl (g (V_SPR_PTL) spr)))
  (if (= mode (USER_MODE)) ;; translate va to pa
      (if (> vpx ptl)
          (mv t va);pfls 
        (b* (;; unlike in paper pto stores the actual physical address
             ;; of the page in mem and not its index
             (pte (g (a+ pto vpx) mem))
             (valid (pte-valid pte))
             (protected (pte-protection pte))
             (ppa (pte-ppage-addr pte)) ;;phy address of the page
             (offset (WX va))
             ((when (or (not valid) 
                        (and w protected)
                        (> (PX ppa) *MAX_PPX*)))
              (mv t va)));raise error
          (mv nil (a+ ppa offset))))
;OTHERWISE system mode (already a physical address)
    (if (> vpx *MAX_PPX*) 
        (mv t va) ;bus error
;o.w already a phy address, no need to translate 
      (mv nil va)))))

(set-verify-guards-eagerness 0)

; Note in ACL2 model imem is not aligned so just increment the offset
; of the program-counter by 1.

; proc -> proc
(defun increment-pcs (p)
  "increment the program counters for proc p"
  (declare (xargs :guard (procp p)))
  (let ((curr-pc (g :pc p)))
    (s :pc (a+ curr-pc 1);(cons (PX curr-pc) (+ 1 (WX curr-pc)))
       (s :dpc curr-pc p))))


;;privileged instructions

;inst * proc -> (il * proc)
(defun exec-movi2s(I p)
  "execute special-purpose register writes, 
   raise illegal exception if called in user mode"
  (b* ((sri (g :sa I)) ;ASSUME R-type Instruction
       ((unless (and (sys-mode? p) (SPRip sri)))
        (mv 'V_IL_ILLEGAL p))
       (gpr (g :gpr p))
       (spr (g :spr p))
       (rdi (g :rd I))
       (rd-val (g rdi gpr))
       (spr (s sri rd-val spr)) ; This assumes that rd-val has
                                ; appropriate type for the SPR
                                ; register that is being updated(sri).
       (p (s :spr spr p)))
    (mv 'V_IL_NONE (increment-pcs p))))
      

;inst * proc -> (il * proc)
(defun exec-movs2i(I p)
  "execute special-purpose register reads, 
   raise illegal exception if called in user mode"
  (b* ((sri (g :sa I));ASSUME R-type Instruction
       ((unless (and (sys-mode? p) (SPRip sri)))
        (mv 'V_IL_ILLEGAL p))
       (gpr (g :gpr p))
       (spr (g :spr p))
       (rdi (g :rd I))
       (sr-val (g sri spr))
       (p (s :gpr (s rdi sr-val gpr) p)))
    (mv 'V_IL_NONE (increment-pcs p))))

(defmacro V_SISR () '(cons 13 3));TRAP instruction p-addr ASK

;; bjtaken : instr v-proc -> boolean
(defun bjtaken (I proc)
  "return true if I is a taken branch instruction"
  (let ((op (g :op I))
        (reg (if (not (instJp I)) (g :rs1 I) 0)))
    (or (equal op 'j)
        (equal op 'jr)
        (and (equal op 'beqz)
             (equal (g reg (g :gpr proc)) 0)))))

;; target : instr * proc -> v-addr
(defun target (I proc)
  (let ((op (g :op I))
        (dpc (g :dpc proc)))
    (case op
      (j (a+ dpc (g :imm I)))
      (jr (g (g :rs1 I) (g :gpr proc)))
      (beqz (a+ dpc (g :imm I))))))

;; exec-cfi : instr mach -> (il mach)
(defun exec-cfi (I m)
  (let* ((proc (g :p m)))
    (if (bjtaken I proc)
      (mv 'V_IL_NONE
          (s :p (up proc :pc (target I proc) :dpc (g :pc proc)) m))
      (mv 'V_IL_NONE (s :p (increment-pcs proc) m)))))

;; exec-alu : instr mach -> (il mach)
(defun exec-alu (I m)
  (let* ((proc (g :p m))
         (regs (g :gpr proc))
         (op (g :op I))
         (lop (g (g :rs1 I) regs))
         (rop (if (instRp I) 
                  (g (g :rs2 I) regs) 
                (g :imm I)))
         (dest (g :rd I))
         (proc (increment-pcs proc)))
    (cond
     ((or (equal op 'add) (equal op 'addi))
      (mv 'V_IL_NONE (s :p (s :gpr (s dest (+ lop rop) regs) proc) m)))
     ((or (equal op 'sub) (equal op 'subi))
      (mv 'V_IL_NONE (s :p (s :gpr (s dest (- lop rop) regs) proc) m)))
     (t (mv 'V_IL_NONE m)))))

;proc * il -> spr
(defun update-spr-isr (p il)
  "updates the relevant spr registers for isr"
  (let* ((spr (proc-spr p))
         (pc (proc-pc p))
         (dpc (proc-dpc p)))
    (up spr
        (V_SPR_MODE) 0 ;; interrupt service routine executes in System mode
        (V_SPR_EMODE) (g (V_SPR_MODE) spr)
        (V_SPR_EDPC) dpc
        (V_SPR_EPC) pc
        (V_SPR_ECA) il
        (V_SPR_ESR) (g (V_SPR_SR) spr)
        (V_SPR_SR) 0)))

;unlike other instructions we only work with proc state
;;proc * il -> proc
(defun exec-jisr (p il)
  "jump to interrupt service routine"
  (declare (xargs :guard (and (procp p)
                              (ilp il))))
  (up p 
      :dpc (V_SISR) 
      :pc (a+ (V_SISR) 1)
      :spr (update-spr-isr p il)))


;spr -> spr
(defun update-spr-rfe (spr)
  "updates the relevant spr registers for rfe"
  (up spr (V_SPR_SR) (g (V_SPR_ESR) spr)
          (V_SPR_MODE) (g (V_SPR_EMODE) spr)))

;proc -> (il * proc)
(defun exec-rfe (p)
  "execute the returns from exception handler"
  (declare (xargs :guard (procp p)))
  (if (sys-mode? p)
      (let* ((spr (update-spr-rfe (g :spr p)))
             (p (up p :pc  (g (V_SPR_EPC) spr) 
                    :dpc (g (V_SPR_EDPC) spr))))
        (mv 'V_IL_NONE p))
    (mv 'V_IL_ILLEGAL p)))

;inst * mach -> (il * mach)
(defun exec-trap (I m)
  "exec Trap instruction I in machine m"
  (declare (xargs :guard (and (machp m)
                              (instp I))))
  (let* ((p (g :p m))
         (spr-new (s (V_SPR_EDATA) (g :imm I) (g :spr p)))
         (p (s :spr spr-new p))
         (p (increment-pcs p)))
    (mv 'V_IL_TRAP (s :p p m))))

;inst * proc -> v-addr
(defun immI-vaddr (I p)
  "get virtual address encoded in I-type instruction I in proc p"
  (declare (xargs :guard (and (instp I)
                              (procp p))))
  (let* ((gpr (g :gpr p))
         (rs1 (g (g :rs1 I) gpr))
         (imm (g :imm I))
         (va (cond ((or (v-addrp rs1)
                        (p-addrp rs1))
                    (a+ rs1 imm))
                   ((natp rs1)
                    (a+ (cons rs1 0) imm))
                   (t (er hard 'immI-vaddr "expecting a p-addr,v-addr or a nat")))))
    va))

;inst * mach --> il * mach
(defun exec-sw (I m)
  "Execute sw instruction I in machine m"
  (declare (xargs :guard (and (machp m)
                              (instp I))))
  (let* ((proc (g :p m))
         (rdi (g :rd I))
         (rd-val (g rdi (g :gpr proc)));get word(data) stored in rd register
         (mem (g :mem m))
         (store-va (immI-vaddr I proc)))
    (mv-let (erp pa)
            (va-to-pa store-va proc mem t)
            (if erp;error occurred
                (let* ((spr (g :spr proc))
                       (spr-edata (s (V_SPR_EDATA) pa spr))
                       (proc (s :spr spr-edata proc))
                       (m (s :p proc m)))
                  (mv 'V_IL_PFLS m))
              (let ((mem (s pa rd-val mem));write mem location pa in dmem
                    (proc (increment-pcs proc)))
                (mv 'V_IL_NONE (up m :p proc :mem mem)))))))


;inst * mach --> il * mach
;;assume the read access is made to data memory
(defun exec-lw (I m)
  "Execute lw instruction I in machine m"
  (declare (xargs :guard (and (machp m)
                              (instp I))))
  (b* ((proc (g :p m))
       (rdi (g :rd I))
       (gpr (g :gpr proc))
       (mem (g :mem m))
       (load-va (immI-vaddr I proc))
       ((mv erp pa)
        (va-to-pa load-va proc mem nil)))
    (if erp;error occurred
        (let* ((spr (g :spr proc))
               (spr-edata (s (V_SPR_EDATA) pa spr))
               (proc (s :spr spr-edata proc))
               (m (s :p proc m)))
          (mv 'V_IL_PFLS m))
      ;;check rd should never be zero(because its the link register)?
      (let* ((gpr (s rdi (g pa mem) gpr));read mem location pa in dmem
             (proc (s :gpr gpr proc));update proc with updated gpr
             (proc (increment-pcs proc)))
        (mv 'V_IL_NONE (s :p proc m))))))

(defun cfi-instp (I)
  (member-eq (g :op I) '(j jr beqz)))

;inst * mach --> il * mach
(defun exec-instr (I m)
  "Execute instruction I in machine m"
  (declare (xargs :guard (and (machp m)
                              (instp I))))
  (let ((op (g :op I)))
    (cond ((equal op 'nop)
           (mv 'V_IL_NONE (mach (increment-pcs (mach-p m)) (mach-mem m))))
          ((cfi-instp I) (exec-cfi I m))
          ((eq 'movi2s op)
           (mv-let (il p)
                   (exec-movi2s I (mach-p m))
                   (mv il (mach p (mach-mem m)))))
          ((eq 'movs2i op)
           (mv-let (il p)
                   (exec-movs2i I (mach-p m))
                   (mv il (mach p (mach-mem m)))))
          ((eq 'rfe op)
           (mv-let (il p)
                   (exec-rfe (mach-p m))
                   (mv il (mach p (mach-mem m)))))
          ((eq 'trap op) (exec-trap I m))
          ((eq 'lw op) (exec-lw I m))
          ((eq 'sw op) (exec-sw I m))
          (t (exec-alu I m)))))

;proc * imem -> erp * Inst
;; (defun instr-fetch (p mem)
;;   (declare (xargs :guard (and (procp p)
;;                               (dmemp mem))))
;;   "fetch current instruction at imem paddr from pc of p"
;;   (b* ((pc (g :pc p))
;;        ((mv erp pa)
;;         (va-to-pa pc p mem nil)))
;;     (if erp;error occurred
;;         (mv t pa)
;;       (mv nil (g pa mem)))))

;; BOZO instr-fetch below is without address translation. To change as
;; little as possible, I will fetch the instruction using index of
;; p-addr in pc. 
(defun instr-fetch (pc imem)
  (declare (xargs :guard (and (p-addrp pc)
                              (imemp imem))))
  "fetch current instruction at imem paddr from pc of p"
  ;(pa (+ (* (PX pc) *PG_SZ*) (WX pc)))
  (mv nil (g pc imem)))

(defun exec-jisr-il (m il)
  (exec-jisr m il))

;mach * boolean -> (il * mach)
(defun step-mach (m reset)
  "Step function for the machine m"
  (declare (xargs :guard (and (machp m)
                              (booleanp reset))))
  (if reset
      (mv 'V_IL_RESET (s :p (exec-jisr m 'V_IL_RESET) m))
    (b* ((p (g :p m))
         (imem (g :instmem p))
         ((mv pf I) 
          (instr-fetch (g :dpc p) imem))
         ((when pf)
          (mv 'V_IL_PFF (s :p (exec-jisr m 'V_IL_PFF) m)))
         ;; Hack for the scenario when we have finished executing all instructions. Ideally it should be possible to handle the scenario with 
         ;; ((when (null I))
         ;;  (mv 'V_IL_NONE m))
         ((unless (instp I))
          (mv 'V_IL_ILLEGAL (s :p (exec-jisr-il p 'V_IL_ILLEGAL) m)))
         ((mv il m)
          (exec-instr I m)));returns il * m'
      (if (equal il 'V_IL_NONE)
          (mv il m)
        (mv il (s :p (exec-jisr (mach-p m) il) m))))))
