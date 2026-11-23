module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianLatticeFiniteness.HformTracePos
public import Formalism.HermitianLattices.DefsCS
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
public import Formalism.HermitianLattices.HermitianLatticesProofs.FinIntermediate
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound
public import Formalism.HermitianLattices.HermitianLatticesProofs.IsomOfTrace
public import Formalism.HermitianLattices.HermitianLatticesProofs.ShortVectors
public import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix
open scoped ComplexOrder

noncomputable section

namespace PI.HermLatFin.UnitaryGroupMassFormula

variable {E : Type} [Field E] [NumberField E]

section Covol

variable [StarRing E] {n : ℕ}

theorem covol_le (σ : E →+* E) (hst : ∀ a : E, star a = σ a)
    (J : Matrix (Fin n) (Fin n) E) (T : ℕ) (N : ℕ)
    (ι : (Fin n → E) →+ EuclideanSpace ℝ (Fin N))
    (hι : ∀ x y, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ E (hform J x y) : ℚ) : ℝ))
    (M : Submodule (𝓞 E) (Fin n → E)) [DiscreteTopology (Formalism.HermitianLatticesTheory.zmap ι M)]
    [IsZLattice ℝ (Formalism.HermitianLatticesTheory.zmap ι M)] (hM : admitted σ J T M) (hT : 0 < T) :
    ZLattice.covolume (Formalism.HermitianLatticesTheory.zmap ι M) ≤
      Real.sqrt (((T * (NumberField.discr E).natAbs ^ 2 : ℕ) : ℝ) ^ N) := by
  classical
  set e : ℤ := NumberField.discr E with he
  have he0 : e ≠ 0 := NumberField.discr_ne_zero E
  have ecast : ((e.natAbs ^ 2 : ℕ) : E) = ((e : E)) * (e : E) := by
    have h0 : ((e.natAbs ^ 2 : ℕ) : ℤ) = e * e := by rw [Nat.cast_pow, Int.natAbs_sq, sq]
    rw [← Int.cast_natCast, h0, Int.cast_mul]
  have hstar : ∀ r : 𝓞 E, star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) :=
    fun r => ⟨⟨star (algebraMap (𝓞 E) E r), r.isIntegral_coe.map (starRingEnd E).toIntAlgHom⟩, rfl⟩
  have hdual : ∀ y, (∀ x ∈ M, ∃ z : ℤ, Algebra.trace ℚ E (hform J x y) = z) →
      ∀ x ∈ M, IsIntegral ℤ (herm σ J x ((e : E) • y)) := by
    intro y hy x hx
    have hm : ((e : ℤ) : E) * hform J x y ∈ (1 : Submodule (𝓞 E) E) := by
      apply Formalism.HermitianLatticesTheory.genusCovolBound_discr
      intro r
      obtain ⟨s, hs'⟩ := hstar r
      obtain ⟨z, hz⟩ := hy (s • x) (M.smul_mem s hx)
      refine ⟨z, ?_⟩
      rw [← hz]
      congr 1
      rw [← algebraMap_smul E s x, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        starRingEnd_apply, hs', star_star, mul_comm]
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hm
    rw [← hform_eq_herm σ hst, LinearMap.map_smul, smul_eq_mul, ← hr]
    exact RingOfIntegers.isIntegral_coe r
  apply Formalism.HermitianLatticesTheory.genusCovolBound_covol_le (hform J) N ι hι M (T * e.natAbs ^ 2)
    (Nat.mul_pos hT (pow_pos (Int.natAbs_pos.mpr he0) 2))
  intro y y' hy hy'
  have h1 : (T : E) • ((e : E) • y) ∈ M := hM.2.2 _ (hdual y hy)
  have h2 := hdual y' hy' _ h1
  rw [← hform_eq_herm σ hst] at h2
  have key : hform J ((T : E) • ((e : E) • y)) ((e : E) • y') =
      algebraMap ℚ E ((T * e.natAbs ^ 2 : ℕ) : ℚ) * hform J y y' := by
    rw [map_natCast, Nat.cast_mul, ecast]
    simp only [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, starRingEnd_apply, star_intCast,
      star_natCast, smul_eq_mul]
    ring
  rw [key] at h2
  obtain ⟨z, hz⟩ := Formalism.HermitianLatticesTheory.genusCovolBound_trace_int (K := E) ⟨_, h2⟩
  refine ⟨z, ?_⟩
  rw [← hz]
  show _ = Algebra.trace ℚ E (algebraMap ℚ E _ * hform J y y')
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

end Covol

theorem hermLatFin_main : HermLatFin := by
  intro E _ _ n σ J T hσ hJ hT
  classical
  letI : StarRing E := starOf σ (sigma_invol σ hσ)
  have hst : ∀ a : E, star a = σ a := fun _ => rfl
  have hJs : ∀ i j, star (J i j) = J j i := fun i j => herm_hermitian σ hσ J hJ i j
  have hs := hform_isSymm J hJs
  have hpos : ∀ x : Fin n → E, x ≠ 0 → 0 < Algebra.trace ℚ E (hform J x x) :=
    hform_trace_pos σ hst hσ J hJ
  obtain ⟨N, ι, hι, hmul, hlat⟩ := Formalism.HermitianLatticesTheory.traceReal E (Fin n → E) (hform J) hs hpos
  obtain ⟨s, -, hsall⟩ := Formalism.HermitianLatticesTheory.classSetFinite_core Formalism.HermitianLatticesTheory.shortVectors
    Formalism.HermitianLatticesTheory.finIntermediate Formalism.HermitianLatticesTheory.isomOfTrace (hform J) hpos N ι hι hmul 1 one_pos _
    {L | admitted σ J T L}
    (fun M hM x hx y hy => by
      rw [Nat.cast_one, one_mul, hform_eq_herm σ hst]
      exact Submodule.mem_one.mpr ⟨⟨_, hM.2.1 x hx y hy⟩, rfl⟩)
    (fun M hM => hlat M
      { toIsLattice := Submodule.IsLattice.of_fg E hM.1.1
        span_eq_top := hM.1.2 })
    (fun M hM _ _ => covol_le σ hst J T N ι hι M hM hT)
  refine ⟨(s : Set _), s.finite_toSet, fun L hL => ?_⟩
  obtain ⟨N', hN', g, hg, hgN⟩ := hsall L hL
  refine ⟨N', hN', LinearMap.toMatrix' (g : (Fin n → E) →ₗ[E] (Fin n → E)),
    isUJ_of_isom σ hst J _ (fun x y => hg x y), ?_⟩
  rw [← hgN, Formalism.HermitianLatticesTheory.gmap, Submodule.map_coe]
  congr 1
  funext x
  exact LinearMap.toMatrix'_mulVec _ x

end PI.HermLatFin.UnitaryGroupMassFormula
