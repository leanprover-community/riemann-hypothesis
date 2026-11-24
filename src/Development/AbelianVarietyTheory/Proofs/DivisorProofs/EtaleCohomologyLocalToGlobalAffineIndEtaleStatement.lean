module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyLocalToGlobalAffineIndEtale
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
theorem _root_.GlobalTheory.T.etaleCohomology_local_to_global_affine_indEtale : ∀ (q : ℕ) (B : Type) [CommRing B] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of B)) [QuasiCompact f] [QuasiSeparated f], IsUnit (q : B) → ∀ i : ℤ, (∀ (A : Type) [CommRing A] [Algebra B A], SH A → IndEt B A → Eqv _ (sch.map (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B A))))) (tw q i)) → Eqv _ (sch.map f) (tw q i) := by
  first | exact @GlobalTheory.LocGlobIndEt.main | exact GlobalTheory.LocGlobIndEt.main | (intros; apply GlobalTheory.LocGlobIndEt.main <;> assumption)
