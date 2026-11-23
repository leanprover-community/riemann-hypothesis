module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsShiftGen
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TateUniformizationInput
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TorusGraphMaps
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformTorsionIsomorphism
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InjectiveOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcClauseCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.TorusExt GlobalTheory.ArcInputCompare GlobalTheory.ArcDataDescent GlobalTheory.LN
open scoped CategoryTheory.Obj


variable {X X' T : Scheme.{0}} {K : Type} [Fintype K] {L' : LB X'} {L : LB X} {φ : X' ⟶ X}
  {w : LB.Iso L' (L.pull φ)} {a : K → (T ⟶ X')} {b : K → (T ⟶ X)} {ε : K → ℤ}
  {t' : LB.Gen (LB.LinComb L' a ε)} {t : LB.Gen (LB.LinComb L b ε)} {z : Γ(T, ⊤)ˣ}


theorem qkToAkU_of_equiv {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} (hk : 1 ≤ k)
    {p q : QkPt D.toPre F k} (e : QkPt.Equiv D.toPre F p q) {x : TFK (R := R) F ⟶ A.A} (h : QkToAkU U F k p x) :
    QkToAkU U F k q x := by
  obtain ⟨z, hy, g, hι, hadd⟩ := e
  refine fun w₀ hw₀ => ⟨(h w₀ hw₀).1, fun θ hθ => ?_⟩
  obtain ⟨w, hw, H⟩ := (h w₀ hw₀).2 θ hθ
  obtain ⟨w₂, hw₂, H₂⟩ := QkShift.qk_shift globalFns_holds R D.toPre D.tau_bimult F k hk p q z g hy hι hadd w hw
  exact ⟨w₂, hw₂, fun t t' s s' a b c => H₂ s s' (H t t' s s' a b c)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
  {R : Type} [CommRing R] [IsDomain R] {f : O' →+* R} {u : R}


open ArcTransport

variable {a : ArcIn D l β O' b} {P : DegPre R} [Module (𝓞 E) P.X] {φ : P.P.A.left ⟶ a.D₀.P.A.left}
  {w : LB.Iso P.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.X}
  {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F]
  [Field F'] [Algebra (FractionRing R) F'] [Algebra (FractionRing O') F'] (σ : F →+* F')
  (h₁ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
  (h₂ : σ.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F')

variable {oP : letI := H.starRing; P.OAct (𝓞 E)} {he : eSec P.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A}
  (hW : Match a f u P oP φ he w e)
  (hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = algebraMap (FractionRing R) F (algebraMap R _ (f x)))



variable (x : TateUniformizationInput.ArcInput D c β O' b) (hf : Function.Injective f) (hu : u ≠ 0) {I : Ideal R}
  (Δ : UniformTorsionIsomorphism.OData H I) (φ : Δ.D.toPre.P.A.left ⟶ x.P.P.A.left) (w : LB.Iso Δ.D.toPre.P.L (x.P.P.L.pull φ))
  (e : x.P.X ≃ₗ[𝓞 E] Δ.D.toPre.X)


variable {Xo : Moduli D l} (Y : Model Xo c β)


variable {I : Ideal R} {χ : Sp R ⟶ Y.X} {t : SAB H (Sp R)} (m : SABMap t Y.t χ) (P : PELUnif I t)

variable {Y m P}


end GlobalTheory.ArcClauseCompare
