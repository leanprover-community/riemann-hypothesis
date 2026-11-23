module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalBundleOfSymmetricSemiAbelianStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationSpecialFibreStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianAndTqOfIsGt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTripleLinearTorsionIsoStatement
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_pelUnif_of_cdvr : (AllSet fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), U.LG = s.P.L ∧ U.gen = s.gen ∧ HEq U.cubG s.P.c) → Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (t : SAB H (Sp V)) (A : PolAV (Sp (FractionRing V))) (gen : (Over.pullback (jK V)).obj t.G ≅ A.A), IsMonHom gen.hom → (∃ w : LB.Iso (A.L.pull gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK V))), w.IsGen) → (∃ S : SplitExt (Sp (IsLocalRing.ResidueField V)), S.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj t.G)) → ∃ P : PELUnif (maximalIdeal V) t, P.A = A ∧ HEq P.U.gen gen ∧ P.TorsionIso := by
  intro hU h1 h2 h3 h4 h5 hTB hVR hTW hUU E _ _ _ H V _ _ _ hV t A gen hgen ⟨w, hw⟩ ⟨S, ⟨d⟩⟩
  obtain ⟨hdvr, hcomp, hchar⟩ := id hV
  have hnoeth : IsNoetherianRing V := inferInstance
  have hic : IsIntegrallyClosed V := inferInstance
  obtain ⟨P, hPL, -⟩ := GlobalTheory.T.exists_cubical_bundle_of_symmetric_semiAbelian h1 V A t.G t.semi gen hgen t.PP t.cub t.sym
  obtain ⟨r, hr⟩ := thick_zero_factor V
  obtain ⟨Q₀⟩ : Nonempty (TQ (thickObj V (maximalIdeal V) 0 t.G) S.X) :=
    nonempty_tq_pullback_comp r _ hr t.G (TQ.ofGtDatum d)
  obtain ⟨P₀, hP₀⟩ := exists_isLevelCP (maximalIdeal V) 0 P
  have hfree := S.free
  have hfin := S.finite
  have hprim : LBIso P.L.L (cubeLB t.G ![𝟙 t.G, t.act.act H.w0] P.L.L) := by rw [hPL]; exact t.prim
  have heven := GlobalTheory.T.exists_even_cubical_trivialisation_specialFibre h1 V hV A t.G t.semi gen hgen P _ (t.act.hom H.w0) hprim S.X Q₀ P₀ hP₀
  obtain ⟨w', hw'⟩ : ∃ w : LB.Iso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst t.G.hom (jK V))), w.IsGen := by
    rw [hPL]; exact ⟨w, hw⟩
  let s : HidaSetting V A t.G :=
    { cdvr := hV, semi := t.semi, gen := gen, gen_hom := hgen, P := P, wA := w', wA_gen := hw', X := S.X,
      Q₀ := Q₀, P₀ := P₀, lev₀ := hP₀, even₀ := heven }
  obtain ⟨D, U, hL, hg, -⟩ := hU V A t.G s
  obtain ⟨Pu, hD, hA, hPU, hT⟩ := GlobalTheory.T.uniformisation_triple_linear_torsionIso ⟨h1, h2, h3, h4, h5⟩ hTB hVR hTW hUU E H V (maximalIdeal V)
    ⟨hnoeth, inferInstance, hic, hcomp⟩ t D A U (hL.trans hPL)
  refine ⟨Pu, hA, ?_, hT⟩
  subst hD hA
  rw [eq_of_heq hPU]
  exact heq_of_eq hg

end GlobalTheory.UU
