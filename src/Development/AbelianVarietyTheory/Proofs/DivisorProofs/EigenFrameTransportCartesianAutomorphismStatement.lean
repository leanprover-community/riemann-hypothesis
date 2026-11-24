module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrvEqSelf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameTransportCartesianAutomorphism
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.eigenFrame_transport_cartesian_automorphism : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {X' : Scheme.{0}} (p : X' ⟶ Y.X) (G' : Over X') [GrpObj G'] (ψ : G'.left ⟶ Y.t.G.left) (act' : OAct (𝓞 E) G') (b : X' ≅ X') (g : G'.left ⟶ G'.left) (hG : IsGrpPullback G' Y.t.G p ψ), (∀ a, (act'.act a).left ≫ ψ = ψ ≫ (Y.t.act.act a).left) → IsGrpPullback G' G' b.hom g → (∀ a, (act'.act a).left ≫ g = g ≫ (act'.act a).left) → ∀ {R : Type} [CommRing R] (φR : c.F →+* R) (q : Sp R ⟶ X') (x' : Sp R ⟶ Y.X), x' = (q ≫ b.hom) ≫ p → ∀ e : GlobalTheory.ShFam.EigFrame Y φR (q ≫ p), ∃ e' : GlobalTheory.ShFam.EigFrame Y φR x', ∀ τ i, e'.v τ i = GlobalTheory.EqvTrans.trv hG.1 g q (e.v τ i) := by
  first | exact @GlobalTheory.EqvTrans.trv_eigFrame | exact GlobalTheory.EqvTrans.trv_eigFrame | (intros; apply GlobalTheory.EqvTrans.trv_eigFrame <;> assumption)
