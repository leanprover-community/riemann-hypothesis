module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjSpaceMapOfLocalSectionsNoCommonZero
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

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical

theorem _root_.GlobalTheory.T.exists_projSpace_map_of_local_sections_no_common_zero : ∀ (o : Type) [CommRing o] (X Z : Scheme.{0}) (f : X ⟶ Z) (s : Z ⟶ Sp o) (B : LB X) (V : X.Opens) (J : Type) (σ : J → ∀ j, Γ(X, V ⊓ B.U j)) (m : ℕ) (e : Fin (m + 1) ≃ J), (∀ i, σ i ∈ secOn B V) → (∀ x ∈ V, ∃ i j, x ∈ X.basicOpen (σ i j)) → ∃ π : V.toScheme ⟶ PSpace o m, π ≫ PSpace.str o m = (V.ι ≫ f) ≫ s ∧ (∀ (i : Fin (m + 1)) (j : B.ι) (T : V.toScheme.Opens) (hi : T ≤ π ⁻¹ᵁ ProjSpace.chart o m i) (hj : T ≤ V.ι ⁻¹ᵁ (V ⊓ B.U j)), IsUnit ((V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ k, (V.ι.appLE _ T hj).hom (σ (e k) j) = ProjSpace.pullRatio π T i hi k * (V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ V.toScheme) (j : B.ι), ⊤ ≤ (x ≫ V.ι) ⁻¹ᵁ B.U j → Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (x ≫ π) (fun k => valF (x ≫ V.ι) (V ⊓ B.U j) (σ (e k) j)) := by
  first | exact @GlobalTheory.ZH.CoordMap.exists_coordMap | exact GlobalTheory.ZH.CoordMap.exists_coordMap | (intros; apply GlobalTheory.ZH.CoordMap.exists_coordMap <;> assumption)
