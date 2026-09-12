import GeneralAlgorithm
import TableSearchComputable

/-! # Mathlib computability of the general decision (R5, item 2)

`strictDecideG` is primitive recursive in `(k, g)`; hence `Computable`, and
`Strict k` is a computable predicate on the general encoded class for every
degree `k ≥ 2` (`computablePred_Strict_degree`).  Together with
`not_computablePred_Lower_degree` this is the general form of the
decidable/undecidable pair `b_k + 1` versus `b_k`. -/

namespace DisequalityDispersion.Encoded

open Primrec

/-! ### Canonical identifiers -/

theorem sigWith_eq_cases (ids : List ℕ) (nd : Node) :
    Instance.sigWith ids nd = Sum.casesOn (Node.equiv nd) (fun i => Node.src i)
      (fun p => Node.app p.1 (p.2.map (fun a => ids.getD a 0))) := by
  cases nd <;> rfl

theorem primrec_sigWith : Primrec₂ Instance.sigWith := by
  have hf : Primrec fun q : List ℕ × Node => Node.equiv q.2 := Primrec.of_equiv.comp snd
  have hg : Primrec₂ fun (_ : List ℕ × Node) (i : ℕ) => Node.src i :=
    Primrec₂.mk (primrec_node_src.comp snd)
  have hmap : Primrec₂ fun (r : (List ℕ × Node) × (ℕ × List ℕ)) (a : ℕ) => r.1.1.getD a 0 :=
    Primrec₂.mk ((list_getD 0).comp (fst.comp (fst.comp fst)) snd)
  have hh : Primrec₂ fun (q : List ℕ × Node) (p : ℕ × List ℕ) =>
      Node.app p.1 (p.2.map (fun a => q.1.getD a 0)) :=
    Primrec₂.mk (primrec_nodeApp.comp (fst.comp snd) (list_map (snd.comp snd) hmap))
  have := sumCasesOn hf hg hh
  exact this.of_eq (fun q => (sigWith_eq_cases _ _).symm)

/-- Parameters of the first-index search: `((γ, ids), sg)`. -/
abbrev FIParams := (Instance × List ℕ) × Node

theorem firstIndex_eq_rec (p : ℕ → Bool) : ∀ n : ℕ, Instance.firstIndex p n =
    Nat.rec (motive := fun _ => ℕ) 0
      (fun n r => if r < n then r else if p n then n else n + 1) n
  | 0 => rfl
  | n + 1 => by
      show (let r := Instance.firstIndex p n; if r < n then r else if p n then n else n + 1) = _
      simp only [firstIndex_eq_rec p n]

theorem primrec_firstIndex_sig :
    Primrec₂ fun (t : FIParams) (n : ℕ) =>
      Instance.firstIndex (fun i => decide (Instance.sigWith t.1.2 (t.1.1.nodes.getD i (.src 0)) = t.2)) n := by
  have hp : Primrec fun q : FIParams × ℕ =>
      decide (Instance.sigWith q.1.1.2 (q.1.1.1.nodes.getD q.2 (.src 0)) = q.1.2) :=
    (Primrec.eq.comp (primrec_sigWith.comp (snd.comp (fst.comp fst))
      ((list_getD (Node.src 0)).comp (primrec_instance_nodes.comp (fst.comp (fst.comp fst))) snd))
      (snd.comp fst)).decide
  have hpair : Primrec fun r : FIParams × (ℕ × ℕ) => (r.1, r.2.1) :=
    Primrec.pair fst (fst.comp snd)
  have hp' : Primrec fun r : FIParams × (ℕ × ℕ) =>
      decide (Instance.sigWith r.1.1.2 (r.1.1.1.nodes.getD r.2.1 (.src 0)) = r.1.2) := by
    have := hp.comp hpair
    exact this
  have hg : Primrec₂ fun (t : FIParams) (q : ℕ × ℕ) =>
      if q.2 < q.1 then q.2 else
        if decide (Instance.sigWith t.1.2 (t.1.1.nodes.getD q.1 (.src 0)) = t.2) then q.1 else q.1 + 1 := by
    apply Primrec₂.mk
    apply Primrec.ite (c := fun r : FIParams × (ℕ × ℕ) => r.2.2 < r.2.1)
      (nat_lt.comp (snd.comp snd) (fst.comp snd)) (snd.comp snd)
    apply Primrec.ite
      (c := fun r : FIParams × (ℕ × ℕ) =>
        decide (Instance.sigWith r.1.1.2 (r.1.1.1.nodes.getD r.2.1 (.src 0)) = r.1.2) = true)
      (f := fun r : FIParams × (ℕ × ℕ) => r.2.1) (g := fun r : FIParams × (ℕ × ℕ) => r.2.1 + 1)
    · exact Primrec.eq.comp hp' (const true)
    · exact fst.comp snd
    · exact succ.comp (fst.comp snd)
  have := nat_rec (f := fun _ : FIParams => (0 : ℕ)) (const 0) hg
  exact this.of_eq (fun t n =>
    (firstIndex_eq_rec (fun i => decide (Instance.sigWith t.1.2 (t.1.1.nodes.getD i (.src 0)) = t.2))
      n).symm)

theorem primrec_canonStep :
    Primrec fun t : (Instance × List ℕ) × ℕ => t.1.1.canonStep t.1.2 t.2 := by
  have hsg : Primrec fun t : (Instance × List ℕ) × ℕ =>
      Instance.sigWith t.1.2 (t.1.1.nodes.getD t.2 (.src 0)) :=
    primrec_sigWith.comp (snd.comp fst)
      ((list_getD (Node.src 0)).comp (primrec_instance_nodes.comp (fst.comp fst)) snd)
  have hr : Primrec fun t : (Instance × List ℕ) × ℕ =>
      Instance.firstIndex (fun i => decide (Instance.sigWith t.1.2 (t.1.1.nodes.getD i (.src 0)) =
        Instance.sigWith t.1.2 (t.1.1.nodes.getD t.2 (.src 0)))) t.2 :=
    primrec_firstIndex_sig.comp (Primrec.pair fst hsg) snd
  have := Primrec.ite (c := fun t : (Instance × List ℕ) × ℕ =>
      Instance.firstIndex (fun i => decide (Instance.sigWith t.1.2 (t.1.1.nodes.getD i (.src 0)) =
        Instance.sigWith t.1.2 (t.1.1.nodes.getD t.2 (.src 0)))) t.2 < t.2)
    (f := fun t : (Instance × List ℕ) × ℕ => t.1.2.getD (Instance.firstIndex (fun i =>
      decide (Instance.sigWith t.1.2 (t.1.1.nodes.getD i (.src 0)) =
        Instance.sigWith t.1.2 (t.1.1.nodes.getD t.2 (.src 0)))) t.2) 0)
    (g := fun t : (Instance × List ℕ) × ℕ => t.2)
    (nat_lt.comp hr snd) ((list_getD 0).comp (snd.comp fst) hr) snd
  exact this.of_eq (fun t => rfl)

theorem primrec_canonIds : Primrec Instance.canonIds := by
  have hh : Primrec₂ fun (γ : Instance) (q : List ℕ × ℕ) => q.1 ++ [γ.canonStep q.1 q.2] :=
    Primrec₂.mk (list_concat.comp (fst.comp snd)
      (primrec_canonStep.comp (Primrec.pair (Primrec.pair fst (fst.comp snd)) (snd.comp snd))))
  have := list_foldl (f := fun γ : Instance => List.range γ.nodes.length)
    (g := fun _ : Instance => ([] : List ℕ))
    (list_range.comp (list_length.comp primrec_instance_nodes)) (const _) hh
  exact this.of_eq (fun γ => rfl)

theorem primrec_testsDistinct : Primrec₂ Instance.testsDistinct := by
  have hh : Primrec₂ fun (p : Instance × List ℕ) (q : (ℕ × ℕ) × Bool) =>
      (!(p.2.getD q.1.1 0 == p.2.getD q.1.2 0)) && q.2 :=
    Primrec₂.mk (primrec_band.comp (Primrec.not.comp
      (Primrec.beq.comp ((list_getD 0).comp (snd.comp fst) (fst.comp (fst.comp snd)))
        ((list_getD 0).comp (snd.comp fst) (snd.comp (fst.comp snd))))) (snd.comp snd))
  have := list_foldr (f := fun p : Instance × List ℕ => p.1.tests) (g := fun _ => true)
    (primrec_instance_tests.comp fst) (const true) hh
  exact this.of_eq (fun p => by unfold Instance.testsDistinct; rw [list_all_eq_foldr])

/-! ### The cut enumeration -/

theorem primrec_cutB : Primrec fun t : (List ℕ × List ℕ) × ℕ => GInstance.cutB t.1.1 t.1.2 t.2 := by
  have : Primrec fun t : (List ℕ × List ℕ) × ℕ => (t.1.2.getD (t.1.1.getD t.2 0) 0 == 1) :=
    Primrec.beq.comp ((list_getD 0).comp (snd.comp fst) ((list_getD 0).comp (fst.comp fst) snd))
      (const 1)
  exact this.of_eq (fun t => rfl)

/-- Parameters of the reachability step: `((g, (ids, b)), vals)`. -/
abbrev DPParams := (GInstance × (List ℕ × List ℕ)) × List Bool

theorem avoidsStep_eq_cases (g : GInstance) (ids b : List ℕ) (vals : List Bool) (j : ℕ) :
    g.avoidsStep ids b vals j = (!(GInstance.cutB ids b j) &&
      Sum.casesOn (Node.equiv (g.base.nodes.getD j (.src 0))) (fun _ => true)
        (fun p => p.2.any (fun a => vals.getD a false))) := by
  unfold GInstance.avoidsStep
  cases g.base.nodes.getD j (.src 0) <;> rfl

theorem primrec_avoidsStep :
    Primrec fun t : DPParams × ℕ => t.1.1.1.avoidsStep t.1.1.2.1 t.1.1.2.2 t.1.2 t.2 := by
  -- projections
  have p1 : Primrec fun t : DPParams × ℕ => t.1 := fst
  have p11 : Primrec fun t : DPParams × ℕ => t.1.1 := fst.comp p1
  have p111 : Primrec fun t : DPParams × ℕ => t.1.1.1 := fst.comp p11
  have p112 : Primrec fun t : DPParams × ℕ => t.1.1.2 := snd.comp p11
  have p12 : Primrec fun t : DPParams × ℕ => t.1.2 := snd.comp p1
  have p2 : Primrec fun t : DPParams × ℕ => t.2 := snd
  have hcpair : Primrec fun t : DPParams × ℕ => (t.1.1.2, t.2) := Primrec.pair p112 p2
  have hcut0 : Primrec fun t : DPParams × ℕ => GInstance.cutB t.1.1.2.1 t.1.1.2.2 t.2 := by
    have := primrec_cutB.comp hcpair
    exact this
  have hcut : Primrec fun t : DPParams × ℕ => !(GInstance.cutB t.1.1.2.1 t.1.1.2.2 t.2) :=
    Primrec.not.comp hcut0
  have hnodes : Primrec fun t : DPParams × ℕ => t.1.1.1.base.nodes :=
    primrec_instance_nodes.comp (primrec_ginstance_base.comp p111)
  have hnd : Primrec fun t : DPParams × ℕ => t.1.1.1.base.nodes.getD t.2 (.src 0) :=
    (list_getD (Node.src 0)).comp hnodes p2
  have hf : Primrec fun t : DPParams × ℕ => Node.equiv (t.1.1.1.base.nodes.getD t.2 (.src 0)) :=
    Primrec.of_equiv.comp hnd
  have hg : Primrec₂ fun (_ : DPParams × ℕ) (_ : ℕ) => true := Primrec₂.mk (const true)
  have hany : Primrec₂ fun (r : (DPParams × ℕ) × (ℕ × List ℕ)) (q : ℕ × Bool) =>
      r.1.1.2.getD q.1 false || q.2 := by
    have q1 : Primrec fun s : ((DPParams × ℕ) × (ℕ × List ℕ)) × (ℕ × Bool) => s.1 := fst
    have q11 : Primrec fun s : ((DPParams × ℕ) × (ℕ × List ℕ)) × (ℕ × Bool) => s.1.1 := fst.comp q1
    have q112 : Primrec fun s : ((DPParams × ℕ) × (ℕ × List ℕ)) × (ℕ × Bool) => s.1.1.1.2 :=
      p12.comp q11
    have q2 : Primrec fun s : ((DPParams × ℕ) × (ℕ × List ℕ)) × (ℕ × Bool) => s.2 := snd
    have q21 : Primrec fun s : ((DPParams × ℕ) × (ℕ × List ℕ)) × (ℕ × Bool) => s.2.1 := fst.comp q2
    have q22 : Primrec fun s : ((DPParams × ℕ) × (ℕ × List ℕ)) × (ℕ × Bool) => s.2.2 := snd.comp q2
    have h4 := (list_getD false).comp q112 q21
    have h5 := primrec_bor.comp h4 q22
    exact Primrec₂.mk h5
  have hh : Primrec₂ fun (t : DPParams × ℕ) (p : ℕ × List ℕ) =>
      p.2.any (fun a => t.1.2.getD a false) := by
    apply Primrec₂.mk
    have r2 : Primrec fun r : (DPParams × ℕ) × (ℕ × List ℕ) => r.2 := snd
    have r22 : Primrec fun r : (DPParams × ℕ) × (ℕ × List ℕ) => r.2.2 := snd.comp r2
    have := list_foldr (f := fun r : (DPParams × ℕ) × (ℕ × List ℕ) => r.2.2) (g := fun _ => false)
      r22 (const false) hany
    exact this.of_eq (fun r => by rw [list_any_eq_foldr])
  have hcases := sumCasesOn hf hg hh
  have := primrec_band.comp hcut hcases
  exact this.of_eq (fun t => (avoidsStep_eq_cases _ _ _ _ _).symm)

theorem primrec_avoidsDP :
    Primrec fun p : GInstance × (List ℕ × List ℕ) => p.1.avoidsDP p.2.1 p.2.2 := by
  have hpair : Primrec fun q : (GInstance × (List ℕ × List ℕ)) × (List Bool × ℕ) =>
      ((q.1, q.2.1), q.2.2) :=
    Primrec.pair (Primrec.pair fst (fst.comp snd)) (snd.comp snd)
  have hstep : Primrec fun q : (GInstance × (List ℕ × List ℕ)) × (List Bool × ℕ) =>
      q.1.1.avoidsStep q.1.2.1 q.1.2.2 q.2.1 q.2.2 := by
    have := primrec_avoidsStep.comp hpair
    exact this
  have hh : Primrec₂ fun (p : GInstance × (List ℕ × List ℕ)) (q : List Bool × ℕ) =>
      q.1 ++ [p.1.avoidsStep p.2.1 p.2.2 q.1 q.2] :=
    Primrec₂.mk (list_concat.comp (fst.comp snd) hstep)
  have := list_foldl (f := fun p : GInstance × (List ℕ × List ℕ) => List.range p.1.base.nodes.length)
    (g := fun _ => ([] : List Bool))
    (list_range.comp (list_length.comp (primrec_instance_nodes.comp (primrec_ginstance_base.comp fst))))
    (const _) hh
  exact this.of_eq (fun p => rfl)

theorem primrec_outNodes : Primrec GInstance.outNodes := by
  have hx : Primrec GInstance.xNode :=
    list_idxOf.comp (primrec_node_src.comp (primrec_instance_x.comp primrec_ginstance_base))
      (primrec_instance_nodes.comp primrec_ginstance_base)
  have hy : Primrec GInstance.yNode :=
    list_idxOf.comp (primrec_node_src.comp (primrec_instance_y.comp primrec_ginstance_base))
      (primrec_instance_nodes.comp primrec_ginstance_base)
  have := list_append.comp (list_cons.comp hx (list_cons.comp hy (const []))) primrec_ginstance_outs
  exact this.of_eq (fun g => rfl)

theorem primrec_isCutB :
    Primrec fun p : GInstance × (List ℕ × List ℕ) => p.1.isCutB p.2.1 p.2.2 := by
  have hh : Primrec₂ fun (p : GInstance × (List ℕ × List ℕ)) (q : ℕ × Bool) =>
      (!((p.1.avoidsDP p.2.1 p.2.2).getD q.1 false)) && q.2 :=
    Primrec₂.mk (primrec_band.comp (Primrec.not.comp
      ((list_getD false).comp (primrec_avoidsDP.comp fst) (fst.comp snd))) (snd.comp snd))
  have := list_foldr (f := fun p : GInstance × (List ℕ × List ℕ) => p.1.outNodes)
    (g := fun _ => true) (primrec_outNodes.comp fst) (const true) hh
  exact this.of_eq (fun p => by unfold GInstance.isCutB; rw [list_all_eq_foldr])

theorem primrec_cutCard :
    Primrec fun p : GInstance × (List ℕ × List ℕ) => p.1.cutCard p.2.1 p.2.2 := by
  have hstep : Primrec₂ fun (p : GInstance × (List ℕ × List ℕ)) (q : ℕ × List ℕ) =>
      bif (p.2.1.getD q.1 0 == q.1 && p.2.2.getD q.1 0 == 1) then q.1 :: q.2 else q.2 := by
    apply Primrec₂.mk
    apply Primrec.cond
      (c := fun r : (GInstance × (List ℕ × List ℕ)) × (ℕ × List ℕ) =>
        r.1.2.1.getD r.2.1 0 == r.2.1 && r.1.2.2.getD r.2.1 0 == 1)
      (f := fun r : (GInstance × (List ℕ × List ℕ)) × (ℕ × List ℕ) => r.2.1 :: r.2.2)
      (g := fun r : (GInstance × (List ℕ × List ℕ)) × (ℕ × List ℕ) => r.2.2)
    · exact primrec_band.comp
        (Primrec.beq.comp ((list_getD 0).comp (fst.comp (snd.comp fst)) (fst.comp snd)) (fst.comp snd))
        (Primrec.beq.comp ((list_getD 0).comp (snd.comp (snd.comp fst)) (fst.comp snd)) (const 1))
    · exact list_cons.comp (fst.comp snd) (snd.comp snd)
    · exact snd.comp snd
  have hfilt := list_foldr (f := fun p : GInstance × (List ℕ × List ℕ) => List.range p.1.base.nodes.length)
    (g := fun _ => ([] : List ℕ))
    (list_range.comp (list_length.comp (primrec_instance_nodes.comp (primrec_ginstance_base.comp fst))))
    (const _) hstep
  have := list_length.comp hfilt
  refine this.of_eq (fun p => ?_)
  unfold GInstance.cutCard GInstance.cutReps
  rw [List.filter_eq_foldr]

theorem primrec_rhoExec : Primrec GInstance.rhoExec := by
  have hstep : Primrec₂ fun (g : GInstance) (q : List ℕ × ℕ) =>
      if g.isCutB g.base.canonIds q.1 then min (g.cutCard g.base.canonIds q.1) q.2 else q.2 := by
    apply Primrec₂.mk
    have hids : Primrec fun r : GInstance × (List ℕ × ℕ) => (r.1, (r.1.base.canonIds, r.2.1)) :=
      Primrec.pair fst (Primrec.pair (primrec_canonIds.comp (primrec_ginstance_base.comp fst))
        (fst.comp snd))
    apply Primrec.ite
      (c := fun r : GInstance × (List ℕ × ℕ) => r.1.isCutB r.1.base.canonIds r.2.1 = true)
      (f := fun r : GInstance × (List ℕ × ℕ) => min (r.1.cutCard r.1.base.canonIds r.2.1) r.2.2)
      (g := fun r : GInstance × (List ℕ × ℕ) => r.2.2)
    · have hc : Primrec fun r : GInstance × (List ℕ × ℕ) => r.1.isCutB r.1.base.canonIds r.2.1 := by
        have := primrec_isCutB.comp hids
        exact this
      exact Primrec.eq.comp hc (const true)
    · have hc : Primrec fun r : GInstance × (List ℕ × ℕ) => r.1.cutCard r.1.base.canonIds r.2.1 := by
        have := primrec_cutCard.comp hids
        exact this
      exact nat_min.comp hc (snd.comp snd)
    · exact snd.comp snd
  have hall : Primrec fun g : GInstance => allLists 2 g.base.nodes.length :=
    primrec_allLists.comp (const 2)
      (list_length.comp (primrec_instance_nodes.comp primrec_ginstance_base))
  have := list_foldr (g := fun g : GInstance => g.base.nodes.length) hall
    (list_length.comp (primrec_instance_nodes.comp primrec_ginstance_base)) hstep
  exact this.of_eq (fun g => rfl)

/-! ### The decision -/

theorem primrec_strictDecideG : Primrec fun p : ℕ × GInstance => p.2.strictDecideG p.1 := by
  have h1 : Primrec fun p : ℕ × GInstance => decide (2 ≤ p.1) := (nat_le.comp (const 2) fst).decide
  have h2 : Primrec fun p : ℕ × GInstance => p.2.isValid := primrec_ginstance_isValid.comp snd
  have h3 : Primrec fun p : ℕ × GInstance => p.2.base.testsDistinct p.2.base.canonIds :=
    primrec_testsDistinct.comp (primrec_ginstance_base.comp snd)
      (primrec_canonIds.comp (primrec_ginstance_base.comp snd))
  have h4 : Primrec fun p : ℕ × GInstance => decide (p.1 + 1 ≤ p.2.rhoExec) :=
    (nat_le.comp (succ.comp fst) (primrec_rhoExec.comp snd)).decide
  have := primrec_band.comp (primrec_band.comp (primrec_band.comp h1 h2) h3) h4
  exact this.of_eq (fun p => rfl)

theorem computable_strictDecideG (k : ℕ) : Computable (fun g : GInstance => g.strictDecideG k) :=
  (primrec_strictDecideG.comp (Primrec.pair (const k) Primrec.id)).to_comp

/-- **`Strict k` is computable on the general encoded class, for every degree `k ≥ 2`.** -/
theorem computablePred_Strict_degree (k : ℕ) (hk : 2 ≤ k) : ComputablePred (GInstance.Strict k) := by
  refine ComputablePred.computable_iff.mpr ⟨fun g => g.strictDecideG k, computable_strictDecideG k, ?_⟩
  funext g
  apply propext
  exact (g.strictDecideG_iff k hk).symm

end DisequalityDispersion.Encoded
