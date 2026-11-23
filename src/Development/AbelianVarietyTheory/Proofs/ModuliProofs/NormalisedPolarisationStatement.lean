module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormalisedPolarisation
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.normalised_polarisation' : Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (w w' : P.A ⟶ P.A), IsMonHom w → IsMonHom w' → w * w' = 𝟙 P.A → LBIso (cubeLB P.A ![fst P.A P.A ≫ w, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ w'] P.L) → ∀ M : LB P.A.left, M = cubeLB P.A ![𝟙 P.A, w] P.L → M.IsLB ∧ Out.Rigidified P.A M ∧ Out.Sym P.A M ∧ Out.RelAmple P.A M ∧ Out.KTriv P.A M ∧ LBIso (abelian₂ P.A M) (abelian₂ P.A P.L) ∧ LBIso M (cubeLB P.A ![𝟙 P.A, w] M) ∧ LBIso (cubeLB P.A ![fst P.A P.A ≫ w, snd P.A P.A] M) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ w'] M) := by
  first | exact @GlobalTheory.PrimNormPol.normalised_polarisation | exact GlobalTheory.PrimNormPol.normalised_polarisation | (intros; apply GlobalTheory.PrimNormPol.normalised_polarisation <;> assumption)
