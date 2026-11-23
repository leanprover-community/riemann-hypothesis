module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingTorsionBasisSymplectic
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
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.weil_pairing_torsion_basis_symplectic : Out.Laws → Out.Laws2 → ∀ (g N k : ℕ) (Mat : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod k)), ∃ S : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod k), ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (pt : Fin (2 * g) → (Out.baseOver (Sp K) ⟶ P.A)) (ζ : Kˣ) (f s : P.A ⟶ P.A), (k : K) ≠ 0 → IsPrimitiveRoot ζ k → TorsBasis P.A k pt → (∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn (ζ ^ Out.stdSymp g i j))) → IsMonHom f → ActsBy pt f Mat → FormIs P (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) s → ActsBy pt s S := by
  first | exact @GlobalTheory.FormTorsion.exists_matrix_form | exact GlobalTheory.FormTorsion.exists_matrix_form | (intros; apply GlobalTheory.FormTorsion.exists_matrix_form <;> assumption)
