module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BoxLeOfComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyMultilinearMap
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_boxFamily_multilinear_map : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), ∃ bx : MultilinearMap (RingHom.id F) (fun _ : Fin j => Fam D F k) (Fam D' F k), ∀ (s : Fin j → Fam D F k) (S : Fam D' F k), IsBoxFam pD F k S s ↔ S = bx s := by
  intro hG R _ _ j D D' pD F _ _ k
  have hexists := GlobalTheory.BoxFamily.exists_isBoxFam hG R j D D' pD F k
  choose bx hbx using hexists
  refine ⟨⟨bx, fun s i a b => GlobalTheory.BoxLinear.box_add pD (hbx _) (hbx _) (hbx _),
    fun s i c a => GlobalTheory.BoxLinear.box_smul pD (hbx _) (hbx _)⟩,
    fun s S => ⟨fun h => GlobalTheory.BoxLinear.box_unique pD h (hbx s), ?_⟩⟩
  rintro rfl
  exact hbx s
