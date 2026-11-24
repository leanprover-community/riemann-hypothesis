module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.KatoTwoOfUseN
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.AdmissibleTwistByDet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.Base GlobalTheory.Ord2

namespace UpperTheory.V.Z.Kato

theorem Used.adm {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K]
    [Algebra K Ω] {e N : ℕ} {θ ψ : G ℚ Ω →* (Qbar l)ˣ} {W : G ℚ Ω →* GL (Fin 2) (Qbar l)} (u : Used l Ω K e N θ ψ W)
    {ι : Qbar l ≃+* ℂ} {f : Af.Newform (2 * e + 1)} (hf : f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) :
    dt W = θ ∧ GlobalTheory.Ord2.admitted ι e W := by
  have hdt : dt W = θ := MonoidHom.ext fun g => Units.ext (u.det g)
  refine ⟨hdt, u.level.cont, ?_, fun s hs => ?_, ?_, ⟨_, ?_, u.level.away⟩, ⟨f, 1, 1, le_rfl, fun _ _ => rfl, ?_⟩, ?_⟩
  · rw [hdt]
    exact MonoidHom.ext u.θ_sq
  · rw [hdt]
    obtain ⟨φ, hφ⟩ := hs
    let : IsTotallyComplex K := u.imag
    have h3 : (θ s : Qbar l) * θ s = 1 := by rw [← sq, ← Units.val_pow_eq_pow_val, u.θ_sq s, Units.val_one]
    refine Units.ext ((mul_self_eq_one_iff.1 h3).resolve_left fun h => ?_)
    have h1 : s ∈ galOf ℚ K Ω := u.θ_ker ▸ (Units.ext h : θ s = 1)
    refine IsTotallyComplex.complexEmbedding_not_isReal (φ.comp (algebraMap K Ω)) ?_
    rw [ComplexEmbedding.isReal_iff]
    apply RingHom.ext
    intro x
    simp only [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hφ, h1 x]
  · refine IrrTransfer.isIrr_of_range _ _ ?_ u.irr
    rintro ⟨τ, hτ⟩
    have hmem : galEmb ℚ K Ω τ ∈ H0g W := by
      refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hτ : _), ?_⟩
      rw [hdt, u.θ_ker]
      exact galEmb_mem ℚ K Ω τ
    exact ⟨⟨_, hmem⟩, rfl⟩
  · exact Nat.mul_pos u.N_pos (Int.natAbs_pos.2 (discr_ne_zero K))
  · rw [mul_one]
    exact hf
  · rw [hdt]
    exact u.flag

end UpperTheory.V.Z.Kato
