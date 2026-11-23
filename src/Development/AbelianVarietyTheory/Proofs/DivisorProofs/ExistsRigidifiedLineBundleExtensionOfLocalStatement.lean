module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedLineBundleExtensionOfLocal
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_rigidifiedLineBundle_extension_of_local : ∀ {S Y U YU : Scheme.{0}} [IsLocallyNoetherian S] [GlobalTheory.IsNormalScheme S] (f : Y ⟶ S) [Smooth f] [GeometricallyConnected f] (j : U ⟶ S) [IsOpenImmersion j], Dense (Set.range j) → ∀ (e : YU ⟶ Y) (fU : YU ⟶ U), IsPullback e fU f j → ∀ (σ : S ⟶ Y) (σU : U ⟶ YU), σ ≫ f = 𝟙 S → σU ≫ e = j ≫ σ → ∀ (L : LB YU), L.IsLB → ∀ (r : LB.Gen (L.pull σU)), r.IsGen → (∀ x : S, x ∉ Set.range j → ∃ W : S.Opens, x ∈ W ∧ ∃ N : LB ↑(f ⁻¹ᵁ W), N.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ ↑(f ⁻¹ᵁ W)) (b : T ⟶ YU), a ≫ (f ⁻¹ᵁ W).ι = b ≫ e → LBIso (N.pull a) (L.pull b)) → ∃ M : LB Y, M.IsLB ∧ LBIso (M.pull e) L := by
  first | exact @GlobalTheory.RigLBDense.exists_extension_of_local_ext | exact GlobalTheory.RigLBDense.exists_extension_of_local_ext | (intros; apply GlobalTheory.RigLBDense.exists_extension_of_local_ext <;> assumption)
