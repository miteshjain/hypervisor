(in-package "ACL2S")
(include-book "baby")

(set-verify-guards-eagerness 0)
;guest * proc -> guest'
(defun save-guest (gst proc)
  (declare (xargs :guard (and (guestp gst)
                              (procp proc))))
  "h is hosting a guest, this function saves the relevant
   registers into pcb of that guest"
  (let* (;; host processor state to be saved
         (gpr (g :gpr proc))
         (spr (g :spr proc))
         (pc (g (V_SPR_EPC) spr))
         (dpc (g (V_SPR_EDPC) spr))
         (pcb (g :pcb gst)))
    ;gst->pcb->spr does not change
    (s :pcb (up pcb :pc pc :dpc dpc :gpr gpr) gst)))

;proc * guest -> proc'
(defun restore-guest-to-host-proc (proc gst)
  (declare (xargs :guard (and (guestp gst)
                              (procp proc))))
  "set up gst pcb in host proc state h"
  (let* ((pcb (g :pcb gst))
         (ggpr (g :gpr pcb))
         (gspr (g :spr pcb))
         (gpc (g :pc pcb))
         (gdpc (g :dpc pcb)) 
         (imem (proc-instmem pcb))
         (proc1 (up proc :pc gpc :dpc gdpc :gpr ggpr :instmem imem))
         (spr (up (g :spr proc1)
                  (V_SPR_MODE) 1 ;always USER mode
                  (V_SPR_PTO) (if (sys-mode? pcb)
                                  (g :hpto gst)
                                (g :spto gst))
                  (V_SPR_PTL) (if (sys-mode? pcb)
                                  (g :max-ppx gst)
                                (g (V_SPR_PTL) gspr)))))
    (s :spr spr proc1)))


;il * hypervisor * mach -> il * hvr -> mach
(defun step-sim-guest (il hvr m)
  (declare (xargs :guard (and (ilp il)
                              (hypervisorp hvr)
                              (machp m))))
  "take one guest step"
  (if (equal il 'V_IL_NONE)
      ;; GUEST step ON HOST

      ;;Notice step-mach would let the guest use (in particular
      ;;update) its own page table which defeats the purpose of
      ;;virtualization. However the above statement is not true as the
      ;;guest always runs in USER mode and therefore any "special"
      ;;instruction will result in an appropriate interrupt at which
      ;;point the hypervisor will take over. "Normal" instructions (lw
      ;;and sw) can also access memory and require address
      ;;translation. These instructions must use the translation from
      ;;the hypervisor and NOT the guest page table (i.e use
      ;;shadow-page table if the guest is in user mode or the
      ;;host-page table if the guest is in system mode). This is
      ;;insured by appropriately loading the processor (proc) state of
      ;;pto and ptl registers (restore-guest-to-host-proc function). This register
      ;;are used in va-to-pa function in step-mach to translate the
      ;;virtual guest address to physical address.
      (mv-let (il m)
              (step-mach m nil)
              (mv il hvr m))
    ;;HYPERVISOR emulating a step on behalf on guest
    (let* ((proc (g :p m))
           (gst (save-guest (g :cg hvr) proc))
           (hvr (update-current-guest gst hvr)));update hvr with updated curr guest
      (mv-let 
       (hvr mem)
       (hv-dispatch (g (V_SPR_ECA) (g :spr proc))
                    (g (V_SPR_EDATA) (g :spr proc))
                    hvr 
                    (g :mem m))
       (let* ((m (s :mem mem m)) 
              (proc (restore-guest-to-host-proc proc (g :cg hvr)))
              (m (s :p proc m)))
         (mv 'V_IL_NONE hvr m))))))
;; after hypervisor has emulated the step on behalf of the guest set
;; il = NONE so that we can return back to executing the guest on the
;; host. Even in the case the fault is "real" we have set up the pc on
;; the host (when restoring) to execute the appropriate ISR.
      


;; Refinement

(defdata conc-state (record (hvr . hypervisor)
                            (m . mach)
                            (status . IL)))

;; the following does not give a new constructor abs-state
;; (defdata abs-state mach)
;; so just creating it manually
(defun abs-state (p dmem)
  (mach p dmem))

;; conc-state -> conc-state
(defun conc-step (s)
  (let ((hvr (conc-state-hvr s))
        (m (conc-state-m s))
        (il (conc-state-status s)))
    (mv-let (il nhvr nm)
            (step-sim-guest il hvr m)
            (conc-state nhvr nm il))))

;; abs-state -> abs-state
(defun abs-step (s)
  (mv-let (il nm)
          (step-mach s nil)
          (declare (ignore il))
          nm))
          
      
;; BiG BIG BOZO I am walking down addresses sequentially while memory is pretty
;; fragment (mostly likely). So this ends up being so so slow for
;; example consider the memory with one no data segment, gpt starting
;; at a large pto. I will walk from (cons 0 0) to large pto step by
;; step. do something about it
(defun read-mem (ra i mem wa acc-mem)
  (declare (xargs :guard (and (p-addrp ra) (natp i) (dmemp mem) (p-addrp wa) (dmemp acc-mem))
                  :verify-guards nil))
  (if (or (zp i) (endp mem))
      acc-mem
    (if (g ra mem)
        (read-mem (a+ ra 1) (1- i) (s ra nil mem) (a+ wa 1) (s wa (g ra mem) acc-mem))
      (read-mem (a+ ra 1) (1- i) mem (a+ wa 1) acc-mem))))


;; hvr  * mach --> mach
(defun ref-map (hvr c-mach)
  (declare (xargs :guard (and (hypervisorp hvr) (machp c-mach))
                  :verify-guards nil))
  (let* ((cg (hypervisor-cg hvr))
         ;; get the gpr,pc,dpc from the host proc
         (c-proc (mach-p c-mach))
         (gpr (proc-gpr c-proc))
         (pc (proc-pc c-proc))
         (dpc (proc-dpc c-proc))
         (imem (proc-instmem c-proc))
         ;; get the spr from the pcb of the current guest in the
         ;; hypervisor
         (pcb (guest-pcb cg))
         (spr (proc-spr pcb))
         (s-proc (proc dpc pc gpr spr imem))
         ;; memory
         (i-dmem (mach-mem c-mach))
         ;; assumes hypervisor installs (1) guest memory starting from
         ;; address gmo (2) then installs host page-table from hpto
         ;; (end of guest memory) through hpto + max-ppx (3) and then
         ;; install SPT from spto (end of host page-table) through spto
         ;; + max-vpx
         (gmo (guest-gmo cg))
         (hpto (guest-hpto cg))
         (diff-idx (- (PX hpto) (PX gmo)))
         ;; both gmo and hpto must be page aligned
         (i (*  diff-idx *PG_SZ*))
         (s-mem (read-mem gmo i i-dmem (cons 0 0) nil))
         ;; recursive function not good for testing. An alternative is
         ;; to record access access to guest memory (listof
         ;; (address,rd/wr,data)) and compare it with the
         ;; corresponding record on the spec machince.
         )
    (mach s-proc s-mem)))

;; conc-state -> abs-state
(defun conc-to-abs (s)
  (declare (xargs :guard (conc-statep s)
                  :verify-guards nil))
  (b* ((hvr (conc-state-hvr s))
       (c-mach (conc-state-m s))
       (il (conc-state-status s))
       (cg (hypervisor-cg hvr))
       ;; get the gpr,pc,dpc from the host proc
       (c-proc (mach-p c-mach))
       (gpr (proc-gpr c-proc))
       (host-spr (proc-spr c-proc))
       ;; BOZO: The folloing refinement of pc and dpc only work in
       ;; case of the current guest.  The host spr register may
       ;; possibly be updated (as a result of restore-guest) with
       ;; another guest. Therefore, pc and dpc should be picked from
       ;; the the pcb of the "corresponding" guest from gsts list. The
       ;; corresponding is defined to be the id of the guest for which
       ;; want the host processor.
       (host-spr-pc (g (V_SPR_EPC) host-spr))
       (host-spr-dpc (g (V_SPR_EDPC) host-spr))
       ((mv pc dpc)
        (if (equal il 'V_IL_NONE)
            (mv (proc-pc c-proc) (proc-dpc c-proc))
          (mv host-spr-pc host-spr-dpc)))
       (imem (proc-instmem c-proc))
       ;; get the spr from the pcb of the current guest in the
       ;; hypervisor
       (pcb (guest-pcb cg))
       (spr (proc-spr pcb))
       (s-proc (proc dpc pc gpr spr imem))
       ;; memory
       (i-dmem (mach-mem c-mach))
       ;; assumes hypervisor installs (1) guest memory starting from
       ;; address gmo (2) then installs host page-table from hpto
       ;; (end of guest memory) through hpto + max-ppx (3) and then
       ;; install SPT from spto (end of host page-table) through spto
       ;; + max-vpx
       (gmo (guest-gmo cg))
       (hpto (guest-hpto cg))
       (diff-idx (- (PX hpto) (PX gmo)))
       ;; both gmo and hpto must be page aligned
       (i (*  diff-idx *PG_SZ*))
       (s-mem (read-mem gmo i i-dmem (cons 0 0) nil))
       ;; recursive function not good for testing. An alternative is
       ;; to record access access to guest memory (listof
       ;; (address,rd/wr,data)) and compare it with the
       ;; corresponding record on the spec machince.
       )
    (mach s-proc s-mem)))
  
    ;(ref-map hvr c-mach)))



;; Rank of the concrete system: In a state when guest is being
;; emulated on the hypervisor (i.e an instruction was executed in
;; previous step which resulted in an IL other than none) , the
;; emulation completes in a single cycle and the conc-state and
;; abs-state should match again.

;; Notes for later: The system can be further refined in (atleast) two
;; following direction:
; (1). Refine the host processor to be pipelined.
; (2). Refine the hypervisor emulation steps (pipeline it as well)

; The rank of such a refined concrete machine can then be given as a
; pair of natural numbers (m,n): where m is the number of steps before
; hypervisor finishes emulating the guest and n is the number of steps
; for the host proc to retire an instruction in pipeline.


;;conc-state -> nat
(defun rank (s)
  " The rank = 0 if guest is emulated in hvr in this step (i.e il !=
  none) else rank = 1"
  (declare (xargs :guard (conc-statep s)))  
  (let ((status (conc-state-status s)))
    (if (equal status 'V_IL_NONE)
        1
      0)))



;; (defthm update-guest-in-gsts-unchanged-lemma
;;   (implies (and (posp i)
;;                 (not (equal (g :id gst)
;;                             i)))
;;            (equal (get-guest-by-id-helper i (update-current-guest-in-gsts gst gsts))
;;                   (get-guest-by-id-helper i gsts))))


;Hypervisor only updates the current guest in the guest list.
;; (defthm hv-dispatch-hvr-same
;;   (implies (and (not (equal eca 'V_IL_RESET))
;;                 (posp id)
;;                 (not (equal id (g :id (g :cg hvr)))))
;;            (equal (get-guest-by-id id (car (hv-dispatch eca edata hvr mem)))
;;                   (get-guest-by-id id hvr)))
;;   :hints (("goal" :in-theory (disable exec-jisr handle-pf 
;;                                       emulate-privileged-operation
;;                                       fetch-PFLS/ILLEGAL-causing-instr))))
                

