module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FamUnit
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FamHomogOfHomog
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleValuationUnitOfFunctorialStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KeyFormulaPowAndDegree
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NonemptyRingHomComplex
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KeyFormulaAndKeyCore
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushforwardPolarisationBundleInvertibleOnModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperRestrictPull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.FlagMod (GChart thUnit thRat detChg pushPP detOm detLie de ev)
open GlobalTheory.Reg (MChart)
open GlobalTheory.LB (toMod)

namespace GlobalTheory.LocM

section OneModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Transport

variable (Y : Model Xo c β) {X : Scheme.{0}} (π : X ⟶ Y.X) [IsIso π]

instance isIso_genInv : IsIso (genInv Y π) := by unfold genInv; infer_instance

@[reducible] def modelOfIso (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (t : SAB H X) (m : SABMap t Y.t π) :
    Model Xo c β where
  X := X
  s := π ≫ Y.s
  normal := hn
  proj := by
    obtain ⟨n, i, hi, e⟩ := Y.proj
    exact ⟨n, π ≫ i, inferInstance, by rw [Category.assoc, e]⟩
  flat := have := Y.flat; inferInstance
  jQ := Y.jQ ≫ genInv Y π
  jQ_over := by rw [Category.assoc, genInv_snd, Y.jQ_over]
  jQ_open := have := Y.jQ_open; inferInstance
  jQ_dense := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]
    exact (genInv Y π).surjective.denseRange.comp Y.jQ_dense (genInv Y π).continuous
  t := t
  oF := Y.oF
  m0 := Y.m0
  m := (exists_sabMap_genInv Y π m).choose
  ab_gen := by
    ext y
    obtain ⟨y, rfl⟩ := (genInv Y π).surjective y
    rw [Set.mem_preimage, ← abLocus_pullback abLocusOne Y.t.semi m.cart.1, ← Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply, genInv_fst, ← Set.mem_preimage, Y.ab_gen]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, Scheme.Hom.comp_apply _ _ _⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, (genInv Y π).homeomorph.injective ((Scheme.Hom.comp_apply _ _ _).symm.trans hx)⟩

end Transport

variable {Y : Model Xo c β}

section Cover

variable [IsNoetherianRing O] (hP : PushInvertible Y.t.G Y.t.PP.L)
include hP

end Cover

def KeyAt (M : GChart Y) {R : Type} [CommRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn R) : Prop :=
  ∃ (φ : x.P.A.left ⟶ Y.t.G.left) (he : eSec x.P.A ≫ φ = z ≫ eSec Y.t.G)
    (w : LB.Iso x.P.L (Y.t.PP.L.pull φ)) (hg : x.P.g = M.n),
    IsGrpPullback x.P.A Y.t.G z φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ z he Y.t.PP.L Y.t.PP.rig) ∧
    (∀ (j : (Y.t.PP.L.pull φ).ι) (i : x.P.L.ι)
      (h : (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U (j PUnit.unit))),
      (φ.appLE _ _ h).hom (M.θ (j PUnit.unit)) =
        (show Γ(x.P.A.left, (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x.th.f i)) ∧
    ∀ i, (x.v i).left ≫ φ = spMap (_root_.Formalism.L2.Pj.dualMap (ev z M.U hz)) ≫ M.v₀ (i.cast hg)

end OneModel

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p)

@[reducible] def base : Model (S.Xo ct.Xm.i.l) ct.Xm.i.c (ct.Xm.i.c.V ct.W).subtype :=
  haveI := ct.B.iso none
  modelOfIso (ct.Y ct.Xm.i) ct.Xm.π (@GlobalTheory.IsNormalScheme.pred _ ct.Xm.normal) ct.Xm.t ct.Xm.tMap

instance isNoetherianRing_base : IsNoetherianRing (ct.Xm.i.c.V ct.W) :=
  GlobalTheory.ModelPresentation.isNoetherianRing_place _ _ ct.hp.ne_zero ct.hW

variable {ct}

variable (ct)

end At

end GlobalTheory.LocM
