module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

private theorem UpperTheory.frobenius_crystalline_eq_unramified {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (x : ↥(K0 K)) :
    (((P.PD K).σ x : ↥(K0 K)) : Om l) = ((frobUr l ⟨x.1, x.2.2⟩ : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  have h1 := (P.PD K).φ_K₀ x
  rw [P.PD_φ] at h1
  have h2 := phiB_algebraMap P ⟨x.1, x.2.2⟩
  have h3 : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨((P.PD K).σ x).1, ((P.PD K).σ x).2.2⟩ =
      algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (frobUr l ⟨x.1, x.2.2⟩) := h1.symm.trans h2
  have : Nontrivial P.R.B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply (P.PD K).not_mem_filtration_two
    rw [Subsingleton.elim (P.PD K).t 0, map_zero]
    exact zero_mem _
  exact congrArg Subtype.val ((algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective h3)

private theorem UpperTheory.frobenius_crystalline_iterate_eq {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (n : ℕ) (x : ↥(K0 K)) :
    ((((P.PD K).σ)^[n] x : ↥(K0 K)) : Om l) = (((frobUr l ^ n) ⟨x.1, x.2.2⟩ : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', UpperTheory.frobenius_crystalline_eq_unramified, pow_succ', AlgHom.mul_apply]
    exact congrArg (fun c => ((frobUr l c : ↥(MaximalUnramifiedExtension l)) : Om l)) (Subtype.ext ih)

theorem UpperTheory.frobenius_residue_degree_fixes :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw), 0 < resDeg l w ∧ ∀ x : ↥(K0 Bw.Kw), ((P.PD Bw.Kw).σ)^[resDeg l w] x = x := by
  intro l _ P E Ω _ _ _ _ _ A w O _ _ _ Bw h hj
  refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, fun x => Subtype.ext ?_⟩
  · have h1 := one_lt_normV w
    rw [normV_eq_pow (hj.mem_placesOver h), h0, pow_zero] at h1
    exact lt_irrefl _ h1
  · have h1 := weilToGK_frobUr hj (frob h) (a := 1) (b := 0)
      (actsAs_of_deg (by simp)) ⟨x.1, x.2.2⟩
    rw [mul_one, mul_zero, pow_zero] at h1
    rw [UpperTheory.frobenius_crystalline_iterate_eq, ← h1]
    exact mem_GK.mp (weilToGK Bw h (frob h)).2 _ x.2.1
