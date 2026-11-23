module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProperNormalFlagSchemeOfAffineCover
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFrameChangeTriangular

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem _root_.GlobalTheory.T.exists_proper_normal_flagScheme_of_affine_cover : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover (RingHom.id K) s V α c D → (∀ x : X, ∃ b, x ∈ (V b).1) → ∃ (Z : Scheme.{0}) (π : Z ⟶ X) (g : ∀ en : En m, Z ⟶ PSpace K (plN M en.1)) (κ : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ Z)), IsProper π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z ∧ HasPlk (RingHom.id K) V α c π g κ ∧ (∀ b w, IsOpenImmersion (κ b w)) ∧ (∀ z : Z, ∃ b w, z ∈ Set.range (κ b w)) ∧ ∀ (W : Scheme.{0}) (a a' : W ⟶ Z), a ≫ π = a' ≫ π → (∀ en, a ≫ g en = a' ≫ g en) → a = a' := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.exists_properFlag | exact GlobalTheory.FlagMod.FieldFlag.exists_properFlag | (intros; apply GlobalTheory.FlagMod.FieldFlag.exists_properFlag <;> assumption)
