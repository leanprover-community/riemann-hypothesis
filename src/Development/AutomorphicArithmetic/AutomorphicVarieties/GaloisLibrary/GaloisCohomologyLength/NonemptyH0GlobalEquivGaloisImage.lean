module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ContScal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.H0ScalRepInvPowEqTwistInv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LenTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Ranges
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

noncomputable section

namespace UpperTheory.V.LDataCardLeFinrank

theorem contTw : ContTw := fun _ _ _ _ _ _ _ l _ D e =>
  ⟨contScal l _ _ (GlobalTheory.TateLimit.continuous_chi D (-e)), GlobalTheory.TateLimit.contAction_zlTw D e⟩

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

theorem contAction_qzG (e : ℤ) : ContAction (qzG F Ω l e) :=
  contScal l _ _ (Units.continuous_val.comp ((continuous_cycZ F Ω l).zpow (-e)))

omit [IsAlgClosure F Ω] in
theorem above_of_mem (D : LData F Ω l) (v : D.S) : v.1 ∈ Above F l := by
  rw [← D.hS]
  exact Finset.mem_coe.2 v.2

theorem global_fixed_points_eq_twist_fixed_points (D : LData F Ω l) (e : ℤ) :
    H0 (qzTw D e) = KStar.TotallyRealRoots.twistInv l (QZ l) (KStar.TotallyRealRoots.galImage l F) e.natAbs := by
  rw [← (ranges F Ω l D).2.1]
  exact H0_scalRep_inv_pow_eq_twistInv l _ D.chi e

theorem local_fixed_points_eq_twist_fixed_points (D : LData F Ω l) (e : ℤ) (v : D.S) :
    H0 ((qzTw D e).comp (locFam D.S D.A v)) = KStar.TotallyRealRoots.twistInv l (QZ l) (decImage F l (D.A v)) e.natAbs := by
  show H0 (scalRep (QZ l) ((D.chi.comp (locFam D.S D.A v)) ^ (-e))) = _
  rw [H0_scalRep_inv_pow_eq_twistInv, (ranges F Ω l D).2.2 v]

theorem length_H0_global_eq_nu (D : LData F Ω l) (e : ℤ) :
    Module.length ℤ_[l] (H0 (qzTw D e)) = KStar.TotallyRealRoots.nuGal l F e.natAbs := by
  rw [global_fixed_points_eq_twist_fixed_points, KStar.TotallyRealRoots.nuGal_eq_nu]
  exact (lenTwist l _ _).1

theorem length_H0_local_eq_nu (D : LData F Ω l) (e : ℤ) (v : D.S) :
    Module.length ℤ_[l] (H0 ((qzTw D e).comp (locFam D.S D.A v))) =
      KStar.TotallyRealRoots.nu l (decImage F l (D.A v)) e.natAbs := by
  rw [local_fixed_points_eq_twist_fixed_points]
  exact (lenTwist l _ _).1

theorem local_H0_length_eq_sum (D : LData F Ω l) (e : ℤ) :
    sumLocalH0TwistLength D e = ∑ v : D.S, KStar.TotallyRealRoots.nu l (decImage F l (D.A v)) e.natAbs :=
  Finset.sum_congr rfl fun v _ => length_H0_local_eq_nu D e v

theorem isOpen_decImage {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (hv : v ∈ Above F l)
    (hA : IsPlaceOver A v) : IsOpen (decImage F l A : Set ℤ_[l]ˣ) :=
  Subgroup.isOpen_mono (ineImage_le_decImage F l A) (ineOpen F Ω l v A hv hA).1

end

end UpperTheory.V.LDataCardLeFinrank

end
