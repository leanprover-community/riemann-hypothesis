import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import GroundTheory.AutomorphicForms.ContragredientTranspose
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfAdmissibility
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LUnlinkedIrr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatenatedJacquetMultiplicityFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductPermEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubSegmentProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapProductSegments
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAllStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankStandardOfHeredity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivariantFunctionalsEqDualAnnihilator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipBEqUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFilterSuperdiag
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedEqFixedVectors
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentLengthTwoReducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyEquivOfJhMultNeZero
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentLengthTwo
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentationIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdMapInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepSplitIntertwiner
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetLengthOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentInduction

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents Zc Zc.Seg GlobalTheory.BZSeg
open GlobalTheory.Parabolic (Embeds)

namespace GlobalTheory.CompanionTheory.StdSubCusp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def top (Δ : Segment k) : IrrGL k := Δ.first.nu ((Δ.len - 1 : ℕ) : ℂ)

def Emb {p q : ℕ} (a : Fin p → IrrGL k) (b : Fin q → IrrGL k) : Prop :=
  ∃ (N : ℕ) (ha : ∑ i, (a i).1 = N) (hb : ∑ i, (b i).1 = N)
    (f : (prodIrr a ha).IntertwiningMap (prodIrr b hb)), Function.Injective f

theorem Emb.of_equiv {p q N : ℕ} {a : Fin p → IrrGL k} {b : Fin q → IrrGL k} (ha : ∑ i, (a i).1 = N)
    (hb : ∑ i, (b i).1 = N) (h : Nonempty ((prodIrr a ha).Equiv (prodIrr b hb))) : Emb a b := by
  obtain ⟨E⟩ := h
  exact ⟨N, ha, hb, E.toIntertwiningMap, E.toLinearEquiv.injective⟩

theorem Emb.trans {p q r : ℕ} {a : Fin p → IrrGL k} {b : Fin q → IrrGL k} {c : Fin r → IrrGL k} (h : Emb a b)
    (h' : Emb b c) : Emb a c := by
  obtain ⟨N, ha, hb, f, hf⟩ := h
  obtain ⟨N', hb', hc, g, hg⟩ := h'
  obtain rfl : N = N' := hb.symm.trans hb'
  exact ⟨N, ha, hc, g.comp f, hg.comp hf⟩

theorem prod₂_map_injective_right {r t : ℕ} {U W W' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U) {ρ : Representation ℂ (GL (Fin t) k) W}
    {ρ' : Representation ℂ (GL (Fin t) k) W'} (g : ρ.IntertwiningMap ρ') (hg : Function.Injective g) :
    ∃ F : (prod₂ σ ρ).IntertwiningMap (prod₂ σ ρ'), Function.Injective F := by
  have hι : Function.Injective (GlobalTheory.ParIndExact.extTensorMapRight σ g) :=
    Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap hg
  have hι' : Function.Injective (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ g)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hι
  exact ⟨parIndMap (two (stdSum rfl)) (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ g)
    (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom), GlobalTheory.ParIndExact.parIndMap_injective _ _ hι'⟩

end GlobalTheory.CompanionTheory.StdSubCusp

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def toQuot {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (P : Representation ℂ G V)
    (C : Subrepresentation P) : P.IntertwiningMap (subQuot ⊤ C) :=
  ⟨(Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation P).toSubmodule
    LinearMap.id (fun v => trivial), fun g => rfl⟩

theorem toQuot_surjective {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (P : Representation ℂ G V)
    (C : Subrepresentation P) : Function.Surjective (toQuot P C) := by
  intro y
  obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨v, rfl⟩

theorem toQuot_eq_zero_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (P : Representation ℂ G V)
    (C : Subrepresentation P) (v : V) : toQuot P C v = 0 ↔ v ∈ C.toSubmodule := by
  show (Submodule.Quotient.mk _ : _ ⧸ _) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

def incl {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {P : Representation ℂ G V}
    (S : Subrepresentation P) : S.toRepresentation.IntertwiningMap P :=
  ⟨S.toSubmodule.subtype, fun _ => rfl⟩

theorem incl_injective {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {P : Representation ℂ G V}
    (S : Subrepresentation P) : Function.Injective (incl S) := Subtype.val_injective

theorem exists_unique_sub {s N : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N) {V Y₀ Y₁ : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup Y₀] [Module ℂ Y₀] [AddCommGroup Y₁] [Module ℂ Y₁]
    {P : Representation ℂ (GL (Fin N) k) V} (hP : IsSmooth P) (hfl : HasFiniteLength P)
    (hne : (⊥ : Subrepresentation P) ≠ ⊤) (hred : ¬ P.IsIrreducible)
    {τ₀ : Representation ℂ (Levi k fun a => Fin (d a)) Y₀}
    {τ₁ : Representation ℂ (Levi k fun a => Fin (d a)) Y₁}
    (h₀ : τ₀.IsIrreducible) (h₁ : τ₁.IsIrreducible)
    (m₀ : jhMult τ₀ (jac e P) ≤ 1) (m₁ : jhMult τ₁ (jac e P) ≤ 1)
    (hcase : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y]
      (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible → IsSubquotient τ (jac e P) →
        Nonempty (τ.Equiv τ₀) ∨ Nonempty (τ.Equiv τ₁))
    (hF : ∀ S : Subrepresentation P, S.toRepresentation.IsIrreducible →
      ∃ q : (jac e S.toRepresentation).IntertwiningMap τ₀, Function.Surjective q)
    (hQ : ∀ (U : Type) [AddCommGroup U] [Module ℂ U] (Q : Representation ℂ (GL (Fin N) k) U),
      IsSmooth Q → Q.IsIrreducible → IsSubquotient Q P →
        IsSubquotient τ₀ (jac e Q) ∨ IsSubquotient τ₁ (jac e Q))
    (hJ : ∀ S : Subrepresentation P, S.toRepresentation.IsIrreducible →
      HasFiniteLength (jac e S.toRepresentation)) :
    ∃ S : Subrepresentation P, S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation P, S'.toRepresentation.IsIrreducible → S' = S) ∧
      Nonempty ((jac e S.toRepresentation).Equiv τ₀) := by
  classical
  have two_le_one : ¬ (2 : ℕ∞) ≤ 1 := by norm_num
  haveI : WellFoundedLT (Subrepresentation P) := ((hasFiniteLength_iff_wellFounded _).1 hfl).2
  haveI : WellFoundedGT (Subrepresentation P) := ((hasFiniteLength_iff_wellFounded _).1 hfl).1
  haveI : IsAtomic (Subrepresentation P) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  obtain ⟨S, hSa, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation P)).resolve_left hne.symm
  have hS : S.toRepresentation.IsIrreducible := GlobalTheory.CuspFactor.irr_of_atom _ S hSa
  have hStop : S ≠ ⊤ := by
    rintro rfl
    exact hred (isSimpleOrder_iff_isAtom_top.2 hSa)
  obtain ⟨C, hC, hSC⟩ := (eq_top_or_exists_le_coatom S).resolve_left hStop
  have hCi : (subQuot ⊤ C).IsIrreducible := isIrreducible_subQuot hC.covBy_top
  have hf := toQuot_surjective P C
  obtain ⟨q, hq⟩ := hF S hS
  have hsub0 : IsSubquotient τ₀ (jac e S.toRepresentation) := .of_surjective q hq
  have hQs : IsSubquotient (subQuot ⊤ C) P := .of_surjective (toQuot P C) hf
  have hSP : IsSubquotient (jac e S.toRepresentation) (jac e P) :=
    .of_injective (jacMap e (incl S)) (GlobalTheory.JacquetExact.jacMap_injective e hP (incl S) (incl_injective S))
  have hz : ∀ z, toQuot P C (incl S z) = 0 := fun z =>
    (toQuot_eq_zero_iff P C _).2 (hSC z.2)
  have hno : ¬ IsSubquotient τ₀ (jac e (subQuot ⊤ C)) := fun h => two_le_one
    ((GlobalTheory.CompanionTheory.SegFine2.two_le_jhMult_of_map e hP (toQuot P C) hf (incl S) (incl_injective S) hz h₀ hsub0 h).trans m₀)
  have hq1 : IsSubquotient τ₁ (jac e (subQuot ⊤ C)) :=
    (hQ _ _ (hQs.isSmooth hP) hCi hQs).resolve_left hno
  have hno1 : ¬ IsSubquotient τ₁ (jac e S.toRepresentation) := fun h => two_le_one
    ((GlobalTheory.CompanionTheory.SegFine2.two_le_jhMult_of_map e hP (toQuot P C) hf (incl S) (incl_injective S) hz h₁ h hq1).trans m₁)
  refine ⟨S, hS, fun S' hS' => ?_, ?_⟩
  · by_contra hne'
    have ha' : IsAtom S' := by
      have h := isAtom_range hS' (incl S') (incl_injective S')
      have e' : (incl S').range = S' := Subrepresentation.toSubmodule_injective (Submodule.range_subtype _)
      rwa [e'] at h
    have hdis : S ⊓ S' = ⊥ := (hSa.disjoint_of_ne ha' (Ne.symm hne')).eq_bot
    let c : S.toRepresentation.IntertwiningMap (subQuot ⊤ S') :=
      ⟨(toQuot P S').toLinearMap ∘ₗ (incl S).toLinearMap, fun g => LinearMap.ext fun v =>
        ((toQuot P S').isIntertwining _ _ g _)⟩
    have hc : Function.Injective c := (injective_iff_map_eq_zero c).2 fun v hv => by
      have h1 : (v : V) ∈ S'.toSubmodule := (toQuot_eq_zero_iff P S' _).1 hv
      have h2 : (v : V) ∈ (S ⊓ S').toSubmodule := ⟨v.2, h1⟩
      rw [hdis] at h2
      exact Subtype.ext h2
    have h2 : IsSubquotient τ₀ (jac e (subQuot ⊤ S')) :=
      hsub0.trans (.of_injective (jacMap e c) (GlobalTheory.JacquetExact.jacMap_injective e
        ((IsSubquotient.of_surjective (toQuot P S') (toQuot_surjective P S')).isSmooth hP) c hc))
    obtain ⟨q', hq'⟩ := hF S' hS'
    exact two_le_one ((GlobalTheory.CompanionTheory.SegFine2.two_le_jhMult_of_map e hP (toQuot P S') (toQuot_surjective P S')
      (incl S') (incl_injective S') (fun z => (toQuot_eq_zero_iff P S' _).2 z.2) h₀
      (.of_surjective q' hq') h2).trans m₀)
  · have hinj : Function.Injective q := by
      let K : Subrepresentation (jac e S.toRepresentation) := ⟨LinearMap.ker q.toLinearMap, fun g x hx => by
        show q (jac e S.toRepresentation g x) = 0
        rw [q.isIntertwining]
        have hx' : q x = 0 := hx
        rw [hx', map_zero]⟩
      by_contra hni
      have hK : K ≠ ⊥ := fun h => hni ((injective_iff_map_eq_zero q).2 fun x hx => by
        have h1 : x ∈ K.toSubmodule := hx
        rw [h] at h1
        exact h1)
      haveI : WellFoundedLT (Subrepresentation (jac e S.toRepresentation)) :=
        ((hasFiniteLength_iff_wellFounded _).1 (hJ S hS)).2
      haveI : IsAtomic (Subrepresentation (jac e S.toRepresentation)) :=
        isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
      obtain ⟨A, hA, hAK⟩ := (eq_bot_or_exists_atom_le K).resolve_left hK
      have hAi : A.toRepresentation.IsIrreducible := GlobalTheory.CuspFactor.irr_of_atom _ A hA
      have hAs : IsSubquotient A.toRepresentation (jac e S.toRepresentation) :=
        .of_injective (incl A) (incl_injective A)
      rcases hcase _ _ hAi (hAs.trans hSP) with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
      · have hadd := jhMult_exact (incl K) q h₀ (incl_injective K) hq (fun u => u.2)
          (fun v hv => ⟨⟨v, hv⟩, rfl⟩)
        let a : A.toRepresentation.IntertwiningMap K.toRepresentation :=
          ⟨LinearMap.codRestrict K.toSubmodule (incl A).toLinearMap (fun x => hAK x.2), fun g => LinearMap.ext fun x =>
            Subtype.ext ((incl A).isIntertwining _ _ g x)⟩
        have ha : Function.Injective a := fun x y h => incl_injective A (congrArg K.toSubmodule.subtype h)
        have a1 : jhMult τ₀ K.toRepresentation ≠ 0 := jhMult_ne_zero_iff.2
          (IsSubquotient.trans (.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective)
            (.of_injective a ha))
        have a2 : jhMult τ₀ τ₀ ≠ 0 := jhMult_ne_zero_iff.2 (.refl _)
        have h5 := ENat.one_le_iff_ne_zero.2 a1
        have h6 := ENat.one_le_iff_ne_zero.2 a2
        have h7 : (2 : ℕ∞) ≤ jhMult τ₀ (jac e S.toRepresentation) := by
          rw [hadd]
          exact (by norm_num : (2 : ℕ∞) = 1 + 1).le.trans (add_le_add h5 h6)
        exact two_le_one ((h7.trans (GlobalTheory.CompanionTheory.JmMono.jhMult_le_of_isSubquotient τ₀ hSP)).trans m₀)
      · exact hno1 (IsSubquotient.trans
          (.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective) hAs)
    exact ⟨LocGL.equivOfBijective q ⟨hinj, hq⟩⟩

set_option maxHeartbeats 1000000 in

theorem cell_cases (hG : JacquetOfInducedFiltration k) {n N : ℕ} (hn : 0 < n) {X : Fin 2 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin n) k) (X a))
    (hs : ∀ a, IsSmooth (ρ a)) (hc : ∀ a, IsCuspidal (ρ a)) (e : (Σ _ : Fin 2, Fin n) ≃ Fin N)
    (h0 : (piTensor ρ).IsIrreducible) (h1 : (piTensor fun a => ρ (Fin.rev a)).IsIrreducible)
    {Y : Type} [AddCommGroup Y] [Module ℂ Y] {τ : Representation ℂ (Levi k fun _ : Fin 2 => Fin n) Y}
    (hτ : τ.IsIrreducible) (hsub : IsSubquotient τ (jac e (multiProd e ρ))) :
    Nonempty (τ.Equiv (piTensor ρ)) ∨ Nonempty (τ.Equiv (piTensor fun a => ρ (Fin.rev a))) := by
  classical
  haveI : Fintype (SizeMatrix (fun _ : Fin 2 => Fin n) (fun _ : Fin 2 => Fin n)) := Fintype.ofFinite _
  have hsm : IsSmooth (piTensor ρ) := isSmooth_piTensor hs
  have key : ∀ b : SizeMatrix (fun _ : Fin 2 => Fin n) (fun _ : Fin 2 => Fin n),
      ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin n) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin n),
        jhMult τ (cellFunctor f g (piTensor ρ)) ≠ 0 →
          Nonempty (τ.Equiv (piTensor ρ)) ∨ Nonempty (τ.Equiv (piTensor fun a => ρ (Fin.rev a))) := by
    intro b
    by_cases hrow : ∀ i j j', b.1 i j ≠ 0 → b.1 i j' ≠ 0 → j = j'
    · obtain ⟨σ, hσ, hz, hb⟩ := GlobalTheory.RegMult.exists_perm (d := fun _ : Fin 2 => n) (fun _ => hn) b hrow
      rcases GlobalTheory.CompanionTheory.SegFine2.perm_two σ with hσ1 | hσ1
      · have hb' : ∀ i j, b.1 i j = if (Equiv.refl (Fin 2)) j = i then n else 0 := by
          intro i j
          by_cases hij : j = i
          · subst hij
            have h2 := hb j
            rw [hσ1] at h2
            simpa using h2
          · rw [if_neg (show ¬ (Equiv.refl (Fin 2)) j = i from hij)]
            exact hz i j (by rw [hσ1]; exact hij)
        obtain ⟨f, g, ⟨φ⟩⟩ := GlobalTheory.CompanionTheory.CellBij.cell_bij (Equiv.refl (Fin 2)) (fun _ => n) ρ hs b hb'
        refine ⟨f, g, fun hne => Or.inl ?_⟩
        have h2 := jhMult_congr_right τ φ
        exact (GlobalTheory.RegMult.nonempty_equiv_of_jhMult_ne_zero hτ h0 (h2.symm.trans_ne hne)).map Representation.Equiv.symm
      · have hb' : ∀ i j, b.1 i j = if (Fin.revPerm : Equiv.Perm (Fin 2)) j = i then n else 0 := by
          intro i j
          by_cases hij : (Fin.revPerm : Equiv.Perm (Fin 2)) j = i
          · subst hij
            rw [if_pos rfl]
            have h2 := hb ((Fin.revPerm : Equiv.Perm (Fin 2)) j)
            rw [hσ1] at h2
            simpa using h2
          · rw [if_neg hij]
            refine hz i j fun h => hij ?_
            rw [hσ1] at h
            rw [h]
            simp
        obtain ⟨f, g, ⟨φ⟩⟩ := GlobalTheory.CompanionTheory.CellBij.cell_bij (Fin.revPerm : Equiv.Perm (Fin 2)) (fun _ => n) ρ hs b hb'
        refine ⟨f, g, fun hne => Or.inr ?_⟩
        have h2 := jhMult_congr_right τ φ
        exact (GlobalTheory.RegMult.nonempty_equiv_of_jhMult_ne_zero hτ h1 (h2.symm.trans_ne hne)).map Representation.Equiv.symm
    · refine ⟨b.nonempty_rows.some, b.nonempty_cols.some, fun hne => ?_⟩
      exfalso
      push_neg at hrow
      obtain ⟨i, j, j', hj, hj', hjj⟩ := hrow
      rcases lt_or_gt_of_ne hjj with hlt | hlt
      · exact hne (GlobalTheory.RegMult.jhMult_cell_eq_zero_of_row (d := fun _ : Fin 2 => n) hc b hlt hj hj' _ _ hτ)
      · exact hne (GlobalTheory.RegMult.jhMult_cell_eq_zero_of_row (d := fun _ : Fin 2 => n) hc b hlt hj' hj _ _ hτ)
  choose f g hfg using key
  have h3 := jhMult_ne_zero_iff.2 hsub
  rw [multiProd, hG.jhMult_eq e e hsm f g hτ] at h3
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero h3
  exact hfg b hb

end GlobalTheory.CompanionTheory.SegTwo

end
end

section
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem bot_ne_top_of_isSubquotient {s N : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N) {V Y : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y] {P : Representation ℂ (GL (Fin N) k) V}
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) Y} (hτ : τ.IsIrreducible)
    (h : IsSubquotient τ (jac e P)) : (⊥ : Subrepresentation P) ≠ ⊤ := by
  intro hb
  obtain ⟨T, f, hf⟩ := h
  haveI := Model.nontrivial_of_isIrreducible hτ
  obtain ⟨w, hw⟩ := exists_ne (0 : Y)
  obtain ⟨t, rfl⟩ := hf w
  have hV : ∀ v : V, v = 0 := fun v => by
    have h1 : v ∈ (⊤ : Subrepresentation P).toSubmodule := trivial
    rw [← hb] at h1
    exact h1
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ t.1
  have h0 : t = 0 := Subtype.ext (by rw [← hu, hV u]; rfl)
  exact hw (by rw [h0, map_zero])

abbrev clx {n : ℕ} (c : Fin 2 → IrrCl (GL (Fin n) k)) : Fin 2 → IrrGL k := fun a => ⟨n, c a⟩

theorem jm_perm (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n N : ℕ} (c : Fin 2 → IrrCl (GL (Fin n) k))
    (hc : ∀ a, (clx c a).IsCusp) (hinj : Function.Injective (clx c)) (σ : Equiv.Perm (Fin 2))
    (hy : ∑ a, (clx c (σ a)).1 = N) (hd : ∑ a, (clx c a).1 = N) :
    jm (fun a => clx c (σ a)) hy (prodIrr (clx c) hd) = 1 := by
  rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA (clx c) _ hd hy hc fun a => hc _]
  have : {e : Fin 2 ≃ Fin 2 | ∀ a, clx c (σ a) = clx c (e a)} = {σ} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · exact fun h => (Equiv.ext fun a => hinj (h a)).symm
    · rintro rfl a
      rfl
  rw [this, Set.ncard_singleton]
  simp

theorem exists_surjective_jac {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {W : Type} [AddCommGroup W] [Module ℂ W]
    (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} (hρ : ρ.IsIrreducible)
    (S : Subrepresentation (parInd e ρ)) (hS : S.toRepresentation.IsIrreducible) :
    ∃ q : (jac e S.toRepresentation).IntertwiningMap ρ, Function.Surjective q := by
  haveI := GlobalTheory.SmGL.nontrivial_of_irreducible hS
  obtain ⟨v, hv⟩ := exists_ne (0 : S.toSubmodule)
  have h1 := GlobalTheory.CompanionTheory.FrobJm.frobMap_ne_zero e (incl S)
    ⟨v, fun h => hv (incl_injective S (h.trans (map_zero (incl S)).symm))⟩
  exact ⟨_, GlobalTheory.CompanionTheory.FrobJm.surjective_of_ne_zero hρ _ h1⟩

set_option maxHeartbeats 1000000 in

theorem two_cusp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n N : ℕ} (hn : 0 < n)
    (c : Fin 2 → IrrCl (GL (Fin n) k)) (hc : ∀ a, (clx c a).IsCusp) (hinj : Function.Injective (clx c))
    (hd : ∑ a, (clx c a).1 = N) (hred : ¬ (prodIrr (clx c) hd).IsIrreducible) :
    ∃ S : Subrepresentation (prodIrr (clx c) hd), S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (prodIrr (clx c) hd), S'.toRepresentation.IsIrreducible → S' = S) ∧
      Nonempty ((jac (stdBlocks (fun a => (clx c a).1) hd) S.toRepresentation).Equiv
        (piTensor fun a => (clx c a).rep)) := by
  have hy : ∑ a, (clx c ((Fin.revPerm : Equiv.Perm (Fin 2)) a)).1 = N := hd
  have hP : IsSmooth (prodIrr (clx c) hd) := isSmooth_prodIrr _ hd
  have h₀ := GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (clx c)
  have h₁ := GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA fun a => clx c ((Fin.revPerm : Equiv.Perm (Fin 2)) a)
  have m₀ : jm (clx c) hd (prodIrr (clx c) hd) = 1 := jm_perm hA c hc hinj 1 hd hd
  have m₁ := jm_perm hA c hc hinj Fin.revPerm hy hd
  refine exists_unique_sub (stdBlocks (fun a => (clx c a).1) hd) hP
    (GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA _ hd)
    (bot_ne_top_of_isSubquotient _ h₀ (jhMult_ne_zero_iff.1 (ne_of_eq_of_ne m₀ one_ne_zero))) hred h₀ h₁
    m₀.le m₁.le ?_ ?_ ?_ ?_
  · intro Y _ _ τ hτ hs
    exact cell_cases (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).1 (n := n) hn
      (X := fun a => (c a).rep.V) (fun a => (c a).rep.ρ)
      (fun a => (c a).rep.smooth) (fun a => (hc a).2) _ h₀ h₁ hτ hs
  · exact fun S hS => exists_surjective_jac (stdBlocks (fun a => (clx c a).1) hd) h₀ S hS
  · intro U _ _ Q hs hi hsub
    obtain ⟨e', he, h1⟩ := GlobalTheory.T.irreducible_subquotient_cuspidal_permutation hA _ hd hc Q hs hi hsub
    rcases GlobalTheory.CompanionTheory.SegFine2.perm_two e' with rfl | rfl
    · exact Or.inl (jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h1))
    · exact Or.inr (jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h1))
  · intro S hS
    exact (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).2.1 _ _ _ _ _ _
      ((IsSubquotient.of_injective (incl S) (incl_injective S)).isSmooth hP) (hasFiniteLength_of_isIrreducible hS)

theorem concl_of_classes (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {d : ℕ} (hd0 : 0 < d)
    {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Fin 2 → Representation ℂ (GL (Fin d) k) V)
    (c : Fin 2 → IrrCl (GL (Fin d) k)) (hc : ∀ a, (clx c a).IsCusp) (hinj : Function.Injective (clx c))
    (hd : ∑ a, (clx c a).1 = 2 * d) (E : ∀ a, (τ a).Equiv (c a).rep.ρ)
    (H : ¬ (multiProd (GlobalTheory.Published.consecBlocks 2 d) τ).IsIrreducible) :
    ∃ S : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) τ), S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) τ), S'.toRepresentation.IsIrreducible → S' = S) ∧
      Nonempty ((jac (GlobalTheory.Published.consecBlocks 2 d) S.toRepresentation).Equiv (piTensor τ)) := by
  have he : GlobalTheory.Published.consecBlocks 2 d = stdBlocks (fun a => (clx c a).1) hd := by
    refine Equiv.ext ?_
    rintro ⟨a, j⟩
    refine Fin.ext ?_
    refine (GlobalTheory.Published.consecBlocks_val _ _ a j).trans (Eq.trans ?_ (stdBlocks_val (fun a => (clx c a).1) hd a j).symm)
    simp [mul_comm, add_comm]
  rw [he] at H ⊢
  let Φ : (multiProd (stdBlocks (fun a => (clx c a).1) hd) τ).Equiv (prodIrr (clx c) hd) := multiProdEquiv _ E
  exact GlobalTheory.CompanionTheory.SegFine2.exists_sub_of_equiv (stdBlocks (fun a => (clx c a).1) hd) Φ.symm (piTensorEquiv E).symm
    (two_cusp hA hd0 c hc hinj hd fun h => H (GlobalTheory.Parabolic.isIrreducible_of_equiv Φ.symm h))

theorem segment_two : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible) →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ∃ S : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
        S.toRepresentation.IsIrreducible ∧
        (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
          S'.toRepresentation.IsIrreducible → S' = S) ∧
        Nonempty ((jac (GlobalTheory.Published.consecBlocks 2 d) S.toRepresentation).Equiv (piTensor (segTerm σ.ρ 2))) := by
  intro H k _ _ _ _ d hd0 σ hc
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  let Δ : Segment k := ⟨d, hd0, σ.cl, ⟨σ, rfl, hc⟩, 2, two_pos⟩
  let c : Fin 2 → IrrCl (GL (Fin d) k) := fun a => (Δ.term a).2
  have hd : ∑ a, (clx c a).1 = 2 * d := Δ.sum_term_fst
  exact concl_of_classes hA hd0 (segTerm σ.ρ 2) c (fun a => Δ.isCusp_term a)
    (GlobalTheory.CompanionTheory.SegTerm.term_injective hA Δ) hd
    (fun a => (twistEquiv (equivRep σ) _).trans (Δ.first.twEquiv _ (isSmoothChar_absPow _)))
    (H k d hd0 σ hc)

end GlobalTheory.CompanionTheory.SegTwo

end
end

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_length_two_irreducible_sub : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible) →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ∃ S : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
        S.toRepresentation.IsIrreducible ∧
        (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
          S'.toRepresentation.IsIrreducible → S' = S) ∧
        Nonempty ((jac (GlobalTheory.Published.consecBlocks 2 d) S.toRepresentation).Equiv (piTensor (segTerm σ.ρ 2))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SegTwo.segment_two
end

section
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
open GlobalTheory.CompanionTheory.SegFine2 (seg2)

namespace GlobalTheory.CompanionTheory.SegZRep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def FineJacZ (Δ : Segment k) : Prop :=
  ∀ {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsZSeg Δ π →
    (∀ hd : ∑ a, (Δ.term a).1 = N, jm Δ.term hd π = 1) ∧
    ∀ (c : ℕ) (y : Fin c → IrrGL k) (hy : ∑ a, (y a).1 = N), (∀ a, (y a).IsCusp) → 1 ≤ jm y hy π →
      ∃ h : c = Δ.len, ∀ a, y a = Δ.term (Fin.cast h a)

theorem jm_term_prod (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} (hd : ∑ a, (Δ.term a).1 = N) :
    jm Δ.term hd (prodIrr Δ.term hd) = 1 :=
  GlobalTheory.CompanionTheory.SegFine2.jm_perm_prod hA Δ 1 hd hd

theorem exists_isSocle (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} (hd : ∑ a, (Δ.term a).1 = N) :
    ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr Δ.term hd) :=
  GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one hA Δ.term hd (jm_term_prod hA Δ hd).le

theorem exists_class (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) :
    ∃ u : IrrGL k, u.1 = Γ.deg ∧ IsZSeg Γ u.rep := by
  have hd : ∑ a, (Γ.term a).1 = Γ.deg := Γ.sum_term_fst
  obtain ⟨τ, hc⟩ := exists_isSocle hA Γ hd
  exact ⟨IrrGL.of τ.ρ τ.smooth τ.irr, rfl, hd, hc.of_equiv (IrrGL.equivOf _ _ _) (Representation.Equiv.refl _)⟩

theorem jm_term_eq_one (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsZSeg Δ π) (hd : ∑ a, (Δ.term a).1 = N) :
    jm Δ.term hd π = 1 := by
  obtain ⟨hd₀, hc⟩ := hπ
  have hsm : IsSmooth π := hc.isSubquotient.isSmooth (isSmooth_prodIrr _ _)
  obtain ⟨f, hf⟩ := hc.embeds
  haveI := Model.nontrivial_of_isIrreducible hc.1
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine le_antisymm ((GlobalTheory.T.jacquet_multiplicity_subquotient_le Δ.term hd π _ (isSmooth_prodIrr _ hd) hc.isSubquotient).trans
    (jm_term_prod hA Δ hd).le) (GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA Δ.term hd π hsm f ⟨v, fun e => hv (hf (e.trans (map_zero f).symm))⟩)

theorem exists_embedding_of_isSocle {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (P : Representation ℂ G V)
    (Q : Representation ℂ G X) (hc : IsSocle σ P) (hfl : HasFiniteLength Q)
    (hf : ∃ f : Q.IntertwiningMap P, Function.Injective f) (hQ : Nontrivial X) :
    ∃ g : σ.IntertwiningMap Q, Function.Injective g := by
  obtain ⟨f, hf⟩ := hf
  haveI : WellFoundedLT (Subrepresentation Q) := ((hasFiniteLength_iff_wellFounded _).1 hfl).2
  haveI : IsAtomic (Subrepresentation Q) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  have hnt : (⊤ : Subrepresentation Q) ≠ ⊥ := fun hb => by
    obtain ⟨u, hu⟩ := exists_ne (0 : X)
    have h1 : u ∈ (⊥ : Subrepresentation Q) := hb ▸ trivial
    exact hu h1
  obtain ⟨S, hS, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation Q)).resolve_left hnt
  have hirr := GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS
  let ι : S.toRepresentation.IntertwiningMap Q := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  obtain ⟨E⟩ := hc.equiv_of_embeds hirr ⟨f.comp ι, hf.comp Subtype.val_injective⟩
  exact ⟨ι.comp E.symm.toIntertwiningMap, Subtype.val_injective.comp E.symm.toLinearEquiv.injective⟩

theorem prod₂_map_injective_right {r t : ℕ} {U W W' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U) {ρ : Representation ℂ (GL (Fin t) k) W}
    {ρ' : Representation ℂ (GL (Fin t) k) W'} (g : ρ.IntertwiningMap ρ') (hg : Function.Injective g) :
    ∃ F : (prod₂ σ ρ).IntertwiningMap (prod₂ σ ρ'), Function.Injective F := by
  have hι : Function.Injective (GlobalTheory.ParIndExact.extTensorMapRight σ g) :=
    Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap hg
  have hι' : Function.Injective (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ g)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hι
  exact ⟨parIndMap (two (stdSum rfl)) (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ g)
    (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom), GlobalTheory.ParIndExact.parIndMap_injective _ _ hι'⟩

theorem exists_injective_of_prod₂_equiv {r t : ℕ} {U U' W W' A D : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [AddCommGroup A]
    [Module ℂ A] [AddCommGroup D] [Module ℂ D] {σ : Representation ℂ (GL (Fin r) k) U}
    {σ' : Representation ℂ (GL (Fin r) k) U'} {ρ : Representation ℂ (GL (Fin t) k) W}
    {ρ' : Representation ℂ (GL (Fin t) k) W'} {α : Representation ℂ (GL (Fin (r + t)) k) A}
    {δ : Representation ℂ (GL (Fin (r + t)) k) D} (f : σ.IntertwiningMap σ')
    (g : ρ.IntertwiningMap ρ') (hf : Function.Injective f) (hg : Function.Injective g)
    (E : Nonempty ((prod₂ σ ρ).Equiv α)) (H : Nonempty ((prod₂ σ' ρ').Equiv δ)) :
    ∃ F : α.IntertwiningMap δ, Function.Injective F := by
  obtain ⟨E⟩ := E
  obtain ⟨H⟩ := H
  obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.ProdInj.prod₂_map_injective k r t _ _ _ σ σ' ρ f hf
  obtain ⟨G, hG⟩ := prod₂_map_injective_right σ' g hg
  exact ⟨H.toIntertwiningMap.comp ((G.comp F).comp E.symm.toIntertwiningMap),
    H.toLinearEquiv.injective.comp ((hG.comp hF).comp E.symm.toLinearEquiv.injective)⟩

theorem exists_injective_of_equiv {G B C D : Type} [Group G] [AddCommGroup B]
    [Module ℂ B] [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
    {β : Representation ℂ G B} {γ : Representation ℂ G C} {δ : Representation ℂ G D}
    (F : ∃ f : β.IntertwiningMap γ, Function.Injective f) (H : Nonempty (γ.Equiv δ)) :
    ∃ f : β.IntertwiningMap δ, Function.Injective f := by
  obtain ⟨F, hF⟩ := F
  obtain ⟨H⟩ := H
  exact ⟨H.toIntertwiningMap.comp F, H.toLinearEquiv.injective.comp hF⟩

theorem exists_injective_append {p q : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (u v : IrrGL k)
    (hx : ∑ a, (x a).1 = u.1) (hy : ∑ a, (y a).1 = v.1) (h : ∑ a, (Fin.append x y a).1 = u.1 + v.1)
    (hd : ∑ i, (![u, v] i).1 = u.1 + v.1)
    (fu : u.rep.IntertwiningMap (prodIrr x hx)) (hfu : Function.Injective fu)
    (fv : v.rep.IntertwiningMap (prodIrr y hy)) (hfv : Function.Injective fv) :
    ∃ F : (prodIrr ![u, v] hd).IntertwiningMap (prodIrr (Fin.append x y) h), Function.Injective F :=
  exists_injective_of_prod₂_equiv fu fv hfu hfv (nonempty_prod₂_equiv_prodIrr_pair u v hd)
    (GlobalTheory.T.product_irreducible_append_equiv k p q u.1 v.1 x y hx hy h)

theorem subtwo (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsZSeg Δ π) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len) (u v : IrrGL k)
    (hu : IsZSeg (segLow Δ a h0) u.rep) (hv : IsZSeg (segHigh Δ a h1) v.rep) (hd : ∑ i, (![u, v] i).1 = N) :
    ∃ f : π.IntertwiningMap (prodIrr ![u, v] hd), Function.Injective f := by
  have hN : u.1 + v.1 = N := hd.symm ▸ (Fin.sum_univ_two (fun i => (![u, v] i).1)).symm
  subst hN
  obtain ⟨hx, -, fu, hfu, -⟩ := hu
  obtain ⟨hy, -, fv, hfv, -⟩ := hv
  obtain ⟨hΔ, hc⟩ := hπ
  have hlen : (segLow Δ a h0).len + (segHigh Δ a h1).len = Δ.len := by
    show a + (Δ.len - a) = Δ.len
    omega
  have hsum : ∑ i, (Fin.append (segLow Δ a h0).term (segHigh Δ a h1).term i).1 = u.1 + v.1 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    exact congrArg₂ (· + ·) hx hy
  exact exists_embedding_of_isSocle π _ _ hc (GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA _ hd)
    (exists_injective_of_equiv (exists_injective_append _ _ u v hx hy hsum hd fu hfu fv hfv)
      (GlobalTheory.CompanionTheory.SegQuotTwo.nonempty_prodIrr_equiv_of_cast hlen _ Δ.term
        (GlobalTheory.CompanionTheory.SegQuotTwo.append_term Δ a h0 h1 hlen) hsum hΔ))
    (GlobalTheory.CompanionTheory.SegQuotTwo.nontrivial_prodIrr hA _ hd)

theorem equiv_piTensor_term (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) (hF : FineJacZ Γ) (u : IrrGL k)
    (hu : IsZSeg Γ u.rep) (hs : ∑ i, (Γ.term i).1 = u.1) (X : Type) [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Levi k fun i => Fin ((Γ.term i).1)) X) (hi : ρ.IsIrreducible)
    (hsub : IsSubquotient ρ (jac (stdBlocks (fun i => (Γ.term i).1) hs) u.rep)) :
    Nonempty (ρ.Equiv (piTensor fun i => (Γ.term i).rep)) := by
  have hsm : IsSmooth ρ := hsub.isSmooth (isSmooth_jac _ u.2.rep.smooth)
  obtain ⟨σ, ⟨E⟩⟩ := GlobalTheory.T.levi_irreducible_tensor_decomposition hA (fun i => (Γ.term i).1) (⟨X, ρ, hsm, hi⟩ : IrrRep _)
  replace E : ρ.Equiv (piTensor fun a => (σ a).rep.ρ) := E
  suffices hσ : σ = fun a => (Γ.term a).2 by
    subst hσ
    exact ⟨E⟩
  let y : Fin Γ.len → IrrGL k := fun i => ⟨(Γ.term i).1, σ i⟩
  have hy : ∑ a, (y a).1 = u.1 := hs
  have h1 : 1 ≤ jm y hy u.rep := Order.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2
    ((IsSubquotient.of_surjective E.toIntertwiningMap E.toLinearEquiv.surjective).trans hsub))
  choose c x hd hcusp hpos using fun a => GlobalTheory.CompanionTheory.SegFineCons.exists_cusp_word hA (y a)
  have hcat : ∑ i, (concat c x i).1 = u.1 := by
    rw [GlobalTheory.CompanionTheory.SegFineCons.sum_concat_fst, ← hy]
    exact Finset.sum_congr rfl fun a _ => hd a
  have h2 : 1 ≤ jm (concat c x) hcat u.rep := h1.trans
    (GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat hA y hy c x hd hcat hpos u.rep u.2.rep.smooth
      (hasFiniteLength_of_isIrreducible u.2.rep.irr))
  obtain ⟨h, hcon⟩ := (hF u.rep hu).2 _ (concat c x) hcat (fun a => hcusp _ _) h2
  have hc0 : ∀ a, 1 ≤ c a := fun a => by
    refine Nat.one_le_iff_ne_zero.2 fun h0 => ?_
    have : IsEmpty (Fin (c a)) := by rw [h0]; exact Fin.isEmpty
    have h3 : (y a).1 = 0 := by rw [← hd a]; simp
    exact Γ.d_pos.ne' h3
  obtain rfl : c = fun _ => 1 := funext (GlobalTheory.CompanionTheory.SegFineCons.eq_one_of_sum_eq c hc0 h)
  funext a
  have h3 : x a 0 = Γ.term (Fin.cast h (finSigmaFinEquiv ⟨a, 0⟩)) :=
    (GlobalTheory.CompanionTheory.SegFineCons.concat_finSigmaFinEquiv _ x ⟨a, 0⟩).symm.trans (hcon (finSigmaFinEquiv ⟨a, 0⟩))
  have h4 : Γ.term (Fin.cast h (finSigmaFinEquiv ⟨a, 0⟩)) = Γ.term a :=
    congrArg _ (Fin.ext (GlobalTheory.CompanionTheory.SegFineCons.finSigmaFinEquiv_one_val a 0))
  have h5 : x a 0 = y a := GlobalTheory.CompanionTheory.SegFine.eq_of_one_le_jm (y a) (y a).rep (.refl _) (x a) (hd a) (hpos a)
  have h6 : (⟨(Γ.term a).1, σ a⟩ : IrrGL k) = ⟨(Γ.term a).1, (Γ.term a).2⟩ := (h5.symm.trans h3).trans h4
  exact sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) k)) h6

theorem fine_tensor (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) (hF : FineJacZ Γ) (u : IrrGL k)
    (hu : IsZSeg Γ u.rep) (hs : ∑ i, (Γ.term i).1 = u.1) :
    Nonempty ((jac (stdBlocks (fun i => (Γ.term i).1) hs) u.rep).Equiv (piTensor fun i => (Γ.term i).rep)) := by
  have hJ : HasFiniteLength (jac (stdBlocks (fun i => (Γ.term i).1) hs) u.rep) :=
    GlobalTheory.T.jacquet_module_finite_length k _ _ _ _ _ _ u.2.rep.smooth (hasFiniteLength_of_isIrreducible u.2.rep.irr)
  exact GlobalTheory.T.equiv_of_multiplicity_one_unique_factor _ _ (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA Γ.term) hJ ((hF u.rep hu).1 hs)
    fun X _ _ ρ hi hq => equiv_piTensor_term hA Γ hF u hu hs X ρ hi hq

theorem shuffle_step (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsZSeg Δ π) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len)
    (hlow : FineJacZ (segLow Δ a h0)) (hhigh : FineJacZ (segHigh Δ a h1)) {c : ℕ} (y : Fin c → IrrGL k)
    (hy : ∑ i, (y i).1 = N) (hyc : ∀ i, (y i).IsCusp) (h : 1 ≤ jm y hy π) :
    ∃ (f : Fin (segLow Δ a h0).len ↪o Fin c) (g : Fin (segHigh Δ a h1).len ↪o Fin c),
      Disjoint (Set.range f) (Set.range g) ∧ (∀ i, y (f i) = (segLow Δ a h0).term i) ∧
        ∀ j, y (g j) = (segHigh Δ a h1).term j := by
  obtain ⟨u, hu1, hu⟩ := exists_class hA (segLow Δ a h0)
  obtain ⟨v, hv1, hv⟩ := exists_class hA (segHigh Δ a h1)
  have hN : N = Δ.len * Δ.d := by
    obtain ⟨hd, -⟩ := hπ
    rw [← hd, Segment.sum_term_fst]
    rfl
  have hd : ∑ i, (![u, v] i).1 = N := by
    have e1 : (segLow Δ a h0).deg = a * Δ.d := rfl
    have e2 : (segHigh Δ a h1).deg = (Δ.len - a) * Δ.d := rfl
    rw [Fin.sum_univ_two]
    show u.1 + v.1 = N
    rw [hu1, hv1, e1, e2, ← Nat.add_mul, Nat.add_sub_cancel' h1.le, hN]
  obtain ⟨φ, hφ⟩ := subtwo hA Δ π hπ a h0 h1 u v hu hv hd
  have hle := GlobalTheory.T.jacquet_multiplicity_subquotient_le y hy π _ (isSmooth_prodIrr _ hd) (.of_injective φ hφ)
  have hs : ∑ i, ((segLow Δ a h0).term i).1 = u.1 := by rw [Segment.sum_term_fst, hu1]
  have ht : ∑ i, ((segHigh Δ a h1).term i).1 = v.1 := by rw [Segment.sum_term_fst, hv1]
  exact GlobalTheory.CompanionTheory.Shuffle2.shuffle2 hA u v _ _ hs ht Δ.d (fun _ => rfl) (fun _ => rfl) (Segment.isCusp_term _)
    (Segment.isCusp_term _) (fine_tensor hA _ hlow u hu hs) (fine_tensor hA _ hhigh v hv ht) hd y hy hyc (h.trans hle)

theorem term_segLow (Δ : Segment k) (a : ℕ) (h0 : 0 < a) (i : Fin (segLow Δ a h0).len) :
    (segLow Δ a h0).term i = Δ.first.nu (((i : ℕ) : ℕ) : ℂ) := rfl

theorem term_segHigh (Δ : Segment k) (a : ℕ) (h1 : a < Δ.len) (j : Fin (segHigh Δ a h1).len) :
    (segHigh Δ a h1).term j = Δ.first.nu ((a + (j : ℕ) : ℕ) : ℂ) := by
  show (Δ.first.nu ((a : ℕ) : ℂ)).nu ((j : ℕ) : ℂ) = _
  rw [IrrGL.nu_nu]
  push_cast
  rfl

theorem fineJacZ_step (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h3 : 3 ≤ Δ.len)
    (ih : ∀ Δ' : Segment k, Δ'.len < Δ.len → FineJacZ Δ') : FineJacZ Δ := by
  intro N V _ _ π hπ
  refine ⟨jm_term_eq_one hA Δ π hπ, fun c y hy hyc h => ?_⟩
  have hN : N = Δ.len * Δ.d := by
    obtain ⟨hd, -⟩ := hπ
    rw [← hd, Segment.sum_term_fst]
    rfl
  have hl1 : 1 < Δ.len := by omega
  have hl2 : Δ.len - 1 < Δ.len := by omega
  have hl0 : 0 < Δ.len - 1 := by omega
  obtain ⟨f₁, g₁, dis₁, hf₁, hg₁⟩ := shuffle_step hA Δ π hπ 1 one_pos hl1
    (ih _ (show 1 < Δ.len from hl1)) (ih _ (show Δ.len - 1 < Δ.len from hl2)) y hy hyc h
  obtain ⟨f₂, g₂, dis₂, hf₂, hg₂⟩ := shuffle_step hA Δ π hπ (Δ.len - 1) hl0 hl2
    (ih _ (show Δ.len - 1 < Δ.len from hl2)) (ih _ (show Δ.len - (Δ.len - 1) < Δ.len by omega)) y hy hyc h
  have hpos : ∀ a, 0 < (y a).1 := fun a => (hyc a).1
  obtain ⟨cov₁, hc₁⟩ := GlobalTheory.CompanionTheory.SegFine.cover (p := 1) (q := Δ.len - 1) (d := Δ.d) (fun a => (y a).1) hpos
    (by rw [hy, hN, Nat.add_sub_cancel' hl1.le]) f₁ g₁ f₁.injective g₁.injective dis₁
    (fun i => congrArg Sigma.fst (hf₁ i)) (fun i => congrArg Sigma.fst (hg₁ i))
  obtain ⟨cov₂, -⟩ := GlobalTheory.CompanionTheory.SegFine.cover (p := Δ.len - 1) (q := Δ.len - (Δ.len - 1)) (d := Δ.d)
    (fun a => (y a).1) hpos
    (by rw [hy, hN, Nat.add_sub_cancel' hl2.le]) f₂ g₂ f₂.injective g₂.injective dis₂
    (fun i => congrArg Sigma.fst (hf₂ i)) (fun i => congrArg Sigma.fst (hg₂ i))
  have hcl : c = Δ.len := by omega
  subst hcl
  have e : ∀ {m n : ℕ}, m = n → Δ.first.nu ((m : ℕ) : ℂ) = Δ.first.nu ((n : ℕ) : ℂ) := by
    rintro m _ rfl
    rfl
  have hinj : ∀ a b, a < Δ.len → b < Δ.len →
      Δ.first.nu ((Δ.len - 1 - a : ℕ) : ℂ) = Δ.first.nu ((Δ.len - 1 - b : ℕ) : ℂ) → a = b := fun a b ha hb hab => by
    have := congrArg Fin.val (GlobalTheory.T.segment_term_injective hA Δ (a₁ := ⟨Δ.len - 1 - a, by omega⟩) (a₂ := ⟨Δ.len - 1 - b, by omega⟩) hab)
    simp only at this
    omega
  have z₁ : 0 < (segLow Δ 1 one_pos).len := one_pos
  have z₂ : 0 < (segHigh Δ (Δ.len - 1) hl2).len := by
    show 0 < Δ.len - (Δ.len - 1)
    omega
  refine ⟨rfl, fun a => ?_⟩
  refine (GlobalTheory.CompanionTheory.SegFine.word_eq_decreasing Δ.len h3 (fun n => Δ.first.nu ((Δ.len - 1 - n : ℕ) : ℂ)) hinj y
    (g₂ ⟨0, z₂⟩) f₂ (fun a => ?_) ?_ (fun j => ?_) (f₁ ⟨0, z₁⟩) g₁ (fun a => ?_) ?_ (fun j => ?_) a).trans ?_
  · rcases cov₂ a with h | ⟨x, rfl⟩
    · exact Or.inr h
    · have hx : (x : ℕ) < Δ.len - (Δ.len - 1) := x.2
      exact Or.inl (congrArg g₂ (Fin.ext (by show (x : ℕ) = 0; omega)))
  · exact (hg₂ _).trans ((term_segHigh _ _ _ _).trans (e (by simp)))
  · have hj : (j : ℕ) < Δ.len - 1 := j.2
    exact (hf₂ j).trans ((term_segLow _ _ _ _).trans (e (by
      have : ((j : Fin (segLow Δ (Δ.len - 1) hl0).len) : ℕ) = j := rfl
      omega)))
  · rcases cov₁ a with ⟨x, rfl⟩ | h
    · have hx : (x : ℕ) < 1 := x.2
      exact Or.inl (congrArg f₁ (Fin.ext (by show (x : ℕ) = 0; omega)))
    · exact Or.inr h
  · exact (hf₁ _).trans ((term_segLow _ _ _ _).trans (e (by simp)))
  · have hj : (j : ℕ) < Δ.len - 1 := j.2
    exact (hg₁ j).trans ((term_segHigh _ _ _ _).trans (e (by
      have : ((j : Fin (segHigh Δ 1 hl1).len) : ℕ) = j := rfl
      omega)))
  · have ha := a.2
    show _ = Δ.first.nu (((Fin.cast rfl a : Fin Δ.len) : ℕ) : ℂ)
    exact e (by simp only [Fin.val_cast]; omega)

theorem term_single (ρ : IrrGL k) (hρ : ρ.IsCusp) : (Segment.single ρ hρ).term = fun _ => ρ := funext fun a => by
  have h0 : ((a : Fin 1) : ℕ) = 0 := Nat.lt_one_iff.1 a.2
  show ρ.nu (((a : Fin 1) : ℕ) : ℂ) = ρ
  rw [h0]
  exact (show ρ.nu ((0 : ℕ) : ℂ) = ρ by simp)

theorem fineJacZ_one (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h : Δ.len = 1) : FineJacZ Δ := by
  obtain ⟨ρ, hρ, rfl⟩ : ∃ ρ hρ, Δ = Segment.single ρ hρ :=
    ⟨Δ.first, Δ.isCusp_first, Segment.ext_first rfl h⟩
  intro N V _ _ π hπ
  refine ⟨jm_term_eq_one hA _ π hπ, fun c y hy hc h1 => ?_⟩
  obtain ⟨hd, hs⟩ := id hπ
  obtain rfl : ρ.1 = N := by
    have := (Segment.sum_term_fst (Segment.single ρ hρ)).symm.trans hd
    simpa [Segment.deg, Segment.single, Segment.ofFirst] using this
  obtain ⟨hd', hs'⟩ := (single_spec hρ).1
  obtain ⟨φ⟩ := hs'.unique hs
  rcases c with _ | _ | c
  · exact absurd hy (by simpa using hρ.1.ne)
  · have key : ∀ (z : Fin 1 → IrrGL k) (hz : ∑ a, (z a).1 = ρ.1), 1 ≤ jm z hz π →
        ∀ a, z a = ρ := fun z hz h1 a => by
      rw [Subsingleton.elim a 0]
      exact GlobalTheory.CompanionTheory.SegFine.eq_of_one_le_jm ρ π φ z hz h1
    exact ⟨rfl, fun a => (key y hy h1 a).trans (congrFun (term_single ρ hρ) _).symm⟩
  · exact absurd h1 (GlobalTheory.CompanionTheory.SegFine.not_one_le_jm (isCuspidal_of_equiv φ.symm hρ.2) y hy hc)

theorem exists_sub (Δ : Segment k) (H : GlobalTheory.SegmentRepModel.Concl Δ.start.rep.ρ Δ.len) {N : ℕ}
    (hd : ∑ a, (Δ.term a).1 = N) :
    ∃ S : Subrepresentation (prodIrr Δ.term hd), S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (prodIrr Δ.term hd), S'.toRepresentation.IsIrreducible → S' = S) ∧
      Nonempty ((jac (stdBlocks (fun a => (Δ.term a).1) hd) S.toRepresentation).Equiv
        (piTensor fun a => (Δ.term a).rep)) := by
  have hN : N = Δ.len * Δ.d := by
    rw [← hd]
    exact Δ.sum_term_fst
  subst hN
  have he : GlobalTheory.Published.consecBlocks Δ.len Δ.d = stdBlocks (fun _ : Fin Δ.len => Δ.d) hd := by
    refine Equiv.ext ?_
    rintro ⟨a, j⟩
    refine Fin.ext ?_
    refine (GlobalTheory.Published.consecBlocks_val _ _ a j).trans (Eq.trans ?_ (stdBlocks_val (fun _ : Fin Δ.len => Δ.d) hd a j).symm)
    simp [mul_comm, add_comm]
  have H₁ : GlobalTheory.CompanionTheory.SegFine2.SegConcl Δ.start.rep.ρ (GlobalTheory.Published.consecBlocks Δ.len Δ.d) := H
  have H' : GlobalTheory.CompanionTheory.SegFine2.SegConcl Δ.start.rep.ρ (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) := he ▸ H₁
  exact GlobalTheory.CompanionTheory.SegFine2.exists_sub_of_equiv (stdBlocks (fun a => (Δ.term a).1) hd) (segProdEquiv Δ hd)
    (piTensorEquiv fun _ => Δ.first.twEquiv _ (isSmoothChar_absPow _)) H'

theorem fineJacZ_seg2 (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (ρ : IrrGL k) (hρ : ρ.IsCusp)
    (H : GlobalTheory.SegmentRepModel.Concl (seg2 ρ hρ).start.rep.ρ (seg2 ρ hρ).len) : FineJacZ (seg2 ρ hρ) := by
  intro N V _ _ π hπ
  refine ⟨jm_term_eq_one hA _ π hπ, fun c y hy hyc h1 => ?_⟩
  obtain ⟨hd, hc⟩ := id hπ
  obtain ⟨S, hSi, -, ⟨φ⟩⟩ := exists_sub _ H hd
  let ι : S.toRepresentation.IntertwiningMap (prodIrr (seg2 ρ hρ).term hd) :=
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  obtain ⟨E⟩ := hc.equiv_of_embeds hSi ⟨ι, Subtype.val_injective⟩
  let ψ : (jac (stdBlocks (fun a => ((seg2 ρ hρ).term a).1) hd) π).Equiv (piTensor fun a => ((seg2 ρ hρ).term a).rep) :=
    (GlobalTheory.SegmentRepModel.jacCongr _ E.symm).trans φ
  have h2 := h1.trans (GlobalTheory.T.jacquet_multiplicity_subquotient_le y hy π _ (isSmooth_prodIrr _ hd) hc.isSubquotient)
  rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA (seg2 ρ hρ).term y hd hy (seg2 ρ hρ).isCusp_term hyc] at h2
  have hne : {e : Fin c ≃ Fin (seg2 ρ hρ).len | ∀ a, y a = (seg2 ρ hρ).term (e a)}.Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty] at hn
    rw [hn, Set.ncard_empty] at h2
    simp at h2
  obtain ⟨e, he⟩ := hne
  have hc2 : c = 2 := by
    have := Fintype.card_congr e
    rw [Fintype.card_fin, Fintype.card_fin] at this
    exact this
  subst hc2
  rcases GlobalTheory.CompanionTheory.SegFine2.perm_two e with rfl | rfl
  · exact ⟨rfl, he⟩
  · have hyx : y = dec (seg2 ρ hρ) := funext he
    subst hyx
    have h3 : IsSubquotient (piTensor fun a => (dec (seg2 ρ hρ) a).rep)
        (jac (stdBlocks (fun a => ((seg2 ρ hρ).term a).1) hd) π) :=
      jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h1)
    exact absurd (h3.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
      (GlobalTheory.CompanionTheory.SegFine2.not_isSubquotient_dec hA ρ hρ)

theorem fineJacZ_all (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    (H : ∀ (d : ℕ), 0 < d → ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ → GlobalTheory.SegmentRepModel.Concl σ.ρ 2)
    (Δ : Segment k) : FineJacZ Δ := by
  induction h : Δ.len using Nat.strong_induction_on generalizing Δ with
  | _ n ih =>
    have h0 := Δ.len_pos
    obtain h1 | h2 | h3 : n = 1 ∨ n = 2 ∨ 3 ≤ n := by omega
    · exact @fineJacZ_one k _ _ _ _ hA Δ (h.trans h1)
    · have e : seg2 Δ.first Δ.isCusp_first = Δ := Segment.ext_first rfl (h.trans h2).symm
      rw [← e]
      exact @fineJacZ_seg2 k _ _ _ _ hA Δ.first Δ.isCusp_first
        (H _ (seg2 Δ.first Δ.isCusp_first).d_pos _ (seg2 Δ.first Δ.isCusp_first).isCusp_first.2)
    · exact @fineJacZ_step k _ _ _ _ hA Δ (h ▸ h3) fun Δ' hlt => ih _ (h ▸ hlt) Δ' rfl

theorem concl_all (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    (H : ∀ (d : ℕ), 0 < d → ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ → GlobalTheory.SegmentRepModel.Concl σ.ρ 2)
    {d l : ℕ} (hd0 : 0 < d) (hl : 0 < l) (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ) :
    GlobalTheory.SegmentRepModel.Concl σ.ρ l := by
  let Δ : Segment k := ⟨d, hd0, σ.cl, ⟨σ, rfl, hσ⟩, l, hl⟩
  have hd : ∑ a, (Δ.term a).1 = l * d := Δ.sum_term_fst
  obtain ⟨τ, hτ⟩ := exists_isSocle hA Δ hd
  have hu : IsZSeg Δ (IrrGL.of τ.ρ τ.smooth τ.irr).rep :=
    ⟨hd, hτ.of_equiv (IrrGL.equivOf _ _ _) (Representation.Equiv.refl _)⟩
  obtain ⟨ψ⟩ := fine_tensor hA Δ (@fineJacZ_all k _ _ _ _ hA H Δ) (IrrGL.of τ.ρ τ.smooth τ.irr) hu hd
  have he : GlobalTheory.Published.consecBlocks l d = stdBlocks (fun _ : Fin l => d) hd := by
    refine Equiv.ext ?_
    rintro ⟨a, j⟩
    refine Fin.ext ?_
    refine (GlobalTheory.Published.consecBlocks_val _ _ a j).trans (Eq.trans ?_ (stdBlocks_val (fun _ : Fin l => d) hd a j).symm)
    simp [mul_comm, add_comm]
  have Φ : Nonempty ((multiProd (GlobalTheory.Published.consecBlocks l d) (segTerm σ.ρ l)).Equiv (prodIrr Δ.term hd)) := by
    rw [he]
    exact ⟨(multiProdEquiv _ fun _ => twistEquiv (equivRep σ) _).trans (segProdEquiv Δ hd)⟩
  obtain ⟨Φ⟩ := Φ
  refine GlobalTheory.SegmentRepModel.concl_of_isSocle (τ := τ.ρ) (hτ.of_equiv (Representation.Equiv.refl _) Φ.symm) ?_
  rw [he]
  exact ⟨(GlobalTheory.SegmentRepModel.jacCongr _ (IrrGL.equivOf τ.ρ τ.smooth τ.irr)).trans (ψ.trans
    (piTensorEquiv fun _ => (twistEquiv (equivRep σ) _).trans (Δ.first.twEquiv _ (isSmoothChar_absPow _))).symm)⟩

theorem segmentRepresentation_of_two :
    (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
      ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
        ∃ S : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
          S.toRepresentation.IsIrreducible ∧
          (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
            S'.toRepresentation.IsIrreducible → S' = S) ∧
          Nonempty ((jac (GlobalTheory.Published.consecBlocks 2 d) S.toRepresentation).Equiv (piTensor (segTerm σ.ρ 2)))) →
    GlobalTheory.Published.SegmentRepresentation := by
  intro H k _ _ _ _ d l hd hl σ hσ
  exact concl_all PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (fun d' hd' σ' hσ' => H k d' hd' σ' hσ') hd hl σ hσ

end GlobalTheory.CompanionTheory.SegZRep

end
end

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unique_irreducible_sub_length_two : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ∃ S : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
        S.toRepresentation.IsIrreducible ∧
        (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
          S'.toRepresentation.IsIrreducible → S' = S) ∧
        Nonempty ((jac (GlobalTheory.Published.consecBlocks 2 d) S.toRepresentation).Equiv (piTensor (segTerm σ.ρ 2)))) →
  GlobalTheory.Published.SegmentRepresentation := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SegZRep.segmentRepresentation_of_two
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.StdSubTop

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem segmentRepresentation : GlobalTheory.Published.SegmentRepresentation :=
  GlobalTheory.T.unique_irreducible_sub_length_two (GlobalTheory.T.segment_length_two_irreducible_sub GlobalTheory.T.segment_length_two_reducible)

end GlobalTheory.CompanionTheory.StdSubTop

end
end
