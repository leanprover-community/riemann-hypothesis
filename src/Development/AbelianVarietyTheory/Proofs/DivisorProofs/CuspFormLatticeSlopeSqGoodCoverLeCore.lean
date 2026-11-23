module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGaloisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCuspFormPullbackGoodCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverCuspFormPullbackInjectiveDescentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelLiftModuliLawsOfCoreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeOfDifferentSmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC

noncomputable section

namespace GlobalTheory.CoreRing


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem slope_sq_latOver_sub_le : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (T.R j)), LawsJ T → InR D j → Y.Good e o → Dom a n → S ⊆ (T.cuspA j a n : Set (T.R j)) → GoodW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ a n) → GoodW Y.U (xiR D) (fun _ => D.sp.W j) Y.dict (wtZ a n) → slope_sq (Y.nrm (wtZ a n)) (Y.latOver (wtZ a n) S) - 2 * (Real.log |(discr Y.d.c₂.F : ℝ)| / Module.finrank ℚ Y.d.c₂.F) ≤ slope_sq (normW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ a n)) (latW (T.U j) (wtZ a n) ⊓ ((Submodule.span T.Q.c.F S).comap (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype).restrictScalars (𝓞 T.Q.c.F)) := by
  intro D T j Y e o a n S hT hj hY hDom hS hG hG₂
  obtain ⟨hLc, hNc⟩ := GlobalTheory.T.principalLevelLiftModuliLaws_of_core D T j hT hj
  obtain ⟨hLd, hGal, hPull⟩ := GlobalTheory.T.deepLevelCover_principalLevel_laws_galois D T j Y e o hT hj hY hY.unit hY.modelW
  let _ : Algebra T.Q.c.F Y.d.c₂.F := ((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle)).toAlgebra
  obtain ⟨π, hπP, hπli, hπN, hπlat, -, hπD⟩ := GlobalTheory.T.levelCover_cuspForm_pullback_injective_descent D j _ _ _ (T.Q.Xo j) T.Q.c Y.c' Y.hle (T.U j)
    (coreDict T.toCore j) Y.d Y.U Y.dict hLc hLd hY.lev.1 hGal a n hDom hDom.2
  have hTC : IsTotallyComplex T.Q.c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := T.Q.c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩

  let G := wtZ a n
  let U := cuspW (T.Q.Xo j) T.Q.c (T.U j) G
  let W := Y.V G
  -- Reuse the module instances for the rules and cusp forms throughout the span arguments.
  let _ : Module T.Q.c.F (T.R j) := rulModule (T.Q.Xo j) T.Q.c
  let _ : Module Y.d.c₂.F (Rul Y.d.Xo₂ Y.d.c₂) := rulModule Y.d.Xo₂ Y.d.c₂
  let _ : Module T.Q.c.F U := U.module
  let _ : Module Y.d.c₂.F W := W.module
  have hSc : ∀ f ∈ S, f ∈ U := fun f hf => by
    change f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)
    rw [cuspW_wtZ]
    exact hS hf
  have hPf : ∀ f : U, Y.Pull (f : T.R j) (π f : Rul Y.d.Xo₂ Y.d.c₂) := fun f =>
    (hPull a n _ (cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) a n (by rw [← cuspW_wtZ]; exact f.2)) _).2 (hπP f)

  have p0 : Y.Pull (0 : T.R j) (0 : Rul Y.d.Xo₂ Y.d.c₂) := by
    intro k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    simp only [evR, evalAt_zero]
  have pAdd : ∀ r₁ r₂ : Rul Y.d.Xo₂ Y.d.c₂, Y.Pull (0 : T.R j) r₁ → Y.Pull (0 : T.R j) r₂ →
      Y.Pull (0 : T.R j) (r₁ + r₂) := by
    intro r₁ r₂ hr₁ hr₂ k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hr₁ k hA hk y₂ y' y h1 h2 h3 h4
    have e2 := hr₂ k hA hk y₂ y' y h1 h2 h3 h4
    simp only [evR, evalAt_zero, evalAt_add] at e1 e2 ⊢
    rw [e1, e2, add_zero]
  have pSmul : ∀ (c : Y.d.c₂.F) (r : Rul Y.d.Xo₂ Y.d.c₂), Y.Pull (0 : T.R j) r → Y.Pull (0 : T.R j) (c • r) := by
    intro c r hr k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hr k hA hk y₂ y' y h1 h2 h3 h4
    simp only [evR, evalAt_zero, evalAt_smul] at e1 ⊢
    rw [e1, mul_zero]
  have pSub : ∀ (f : T.R j) (g₁ g₂ : Rul Y.d.Xo₂ Y.d.c₂), Y.Pull f g₁ → Y.Pull f g₂ → Y.Pull (0 : T.R j) (g₁ - g₂) := by
    intro f g₁ g₂ hg₁ hg₂ k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hg₁ k hA hk y₂ y' y h1 h2 h3 h4
    have e2 := hg₂ k hA hk y₂ y' y h1 h2 h3 h4
    have e3 : evR Y.d.Xo₂ Y.d.c₂ (g₁ - g₂) y₂ = evR Y.d.Xo₂ Y.d.c₂ g₁ y₂ - evR Y.d.Xo₂ Y.d.c₂ g₂ y₂ :=
      map_sub (evalL (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) y₂) g₁ g₂
    rw [e3, e1, e2, sub_self]
    simp only [evR, evalAt_zero]
  let Z : Submodule Y.d.c₂.F (Rul Y.d.Xo₂ Y.d.c₂) :=
    { carrier := {g | Y.Pull (0 : T.R j) g}
      zero_mem' := p0
      add_mem' := pAdd _ _
      smul_mem' := pSmul }
  let C : Submodule T.Q.c.F U := (Submodule.span T.Q.c.F S).comap U.subtype
  have hCspan : C = Submodule.span T.Q.c.F (U.subtype ⁻¹' S) := by
    change (Submodule.span T.Q.c.F S).comap U.subtype = _
    rw [← Submodule.comap_map_eq_of_injective U.injective_subtype
      (Submodule.span T.Q.c.F (U.subtype ⁻¹' S)), Submodule.map_span,
      Set.image_preimage_eq_of_subset]
    intro f hf
    exact ⟨⟨f, hSc f hf⟩, rfl⟩
  let P := Submodule.span Y.d.c₂.F {g | ∃ f ∈ S, Y.Pull f g}
  have hCQ : C ≤ (P.comap W.subtype).comap π := by
    rw [hCspan]
    apply Submodule.span_le.2
    intro f hf
    exact Submodule.subset_span ⟨(f : T.R j), hf, hPf f⟩
  let Q := Submodule.span Y.d.c₂.F (π '' (C : Set U))
  -- A generator of P differs from the chosen pullback of its source by an element of Z.
  have hP : P ≤ Q.map W.subtype ⊔ Z := by
    apply Submodule.span_le.2
    rintro g ⟨f, hf, hfg⟩
    let x : U := ⟨f, hSc f hf⟩
    have hx : x ∈ C := Submodule.subset_span hf
    have hxQ : π x ∈ Q := Submodule.subset_span ⟨x, hx, rfl⟩
    refine Submodule.mem_sup.2 ⟨(π x : Rul Y.d.Xo₂ Y.d.c₂),
      Submodule.mem_map_of_mem hxQ, g - (π x : Rul Y.d.Xo₂ Y.d.c₂), pSub f _ _ hfg (hPf x), ?_⟩
    exact add_sub_cancel _ _
  let L := latW (T.U j) G ⊓ C.restrictScalars (𝓞 T.Q.c.F)
  let M := Y.latOver G S
  have hu := GlobalTheory.T.existsUnique_cuspForm_pullback_goodCover
    D T j Y e o hT hj hY hY.unit hY.modelW a n hDom 0 U.zero_mem
  have hDiff : ∀ δ ∈ differentIdeal ℤ (𝓞 Y.d.c₂.F), ∀ g ∈ M,
      δ • g ∈ Submodule.span (𝓞 Y.d.c₂.F) (π '' (L : Set U)) := by
    intro δ hδ g hg
    have hgl : g ∈ latW Y.U G := (Submodule.mem_inf.1 hg).1
    have hgP : (g : Rul Y.d.Xo₂ Y.d.c₂) ∈ P := (Submodule.mem_inf.1 hg).2
    obtain ⟨y, hy, z, hz, hsum⟩ := Submodule.mem_sup.1 (hP hgP)
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    have hzW : z ∈ W := by
      have hsub := eq_sub_of_add_eq' hsum
      exact hsub ▸ W.sub_mem g.2 x.2
    have hz0 : z = 0 := hu.unique ⟨hzW, hz⟩ ⟨W.zero_mem, p0⟩
    have hgx : g = x := by
      rw [hz0, add_zero] at hsum
      exact Subtype.ext hsum.symm
    have hgQ : g ∈ Q := hgx.symm ▸ hx
    have hset : {f : U | f ∈ C ∧ f ∈ latW (T.U j) G} = (L : Set U) :=
      Set.ext fun _ => And.comm
    rw [← hset]
    exact hπD C δ hδ g hgl hgQ
  refine GlobalTheory.SlopeDifferent.slope_sq_sub_le_of_different_smul
    (K := T.Q.c.F) (K' := Y.d.c₂.F) (V := U) (V' := W) _ _ π L M hG.1 hG₂.1
    ?_ hπli ?_ ?_ ?_ hDiff
  · intro σ f
    rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ]
  · exact Submodule.FG.of_le hG₂.2.1 (show M ≤ latW Y.U G from inf_le_left)
  · intro σ' x
    exact (hπN σ' x).trans (hNc G _ x)
  · intro x hx
    obtain ⟨hxl, hxC⟩ := Submodule.mem_inf.1 hx
    exact Submodule.mem_inf.2 ⟨(hπlat x).2 hxl, hCQ hxC⟩

end GlobalTheory.CoreRing
