module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.ExistsCorr

@[expose] public section

open AlgebraicGeometry CategoryTheory
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace ModelDimension.Tan

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)

theorem exists_basis {X : Scheme.{0}} (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) {S : Type} [CommRing S]
    [Algebra c.F S] (z : Spec (CommRingCat.of S) ⟶ X) (y : FrPt Xo c S) (hy : Small.ptY Y y = z ≫ f) (τ : E →+* ℂ) :
    ∃ ub : Fin (Dw.mult τ) → (GlobalTheory.CompanionTheory.Ar.epsAt z ⟶ tX.G), (∀ i, (ub i).left ≫ m.φ = Small.tanY Y y τ i) ∧
      (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt tX.G z (ub i)) ∧
      (∀ i a, ub i ≫ tX.act.act a = sc z (algebraMap c.F S (embK c τ a)) ≫ ub i) ∧
      ∀ v : GlobalTheory.CompanionTheory.Ar.epsAt z ⟶ tX.G, GlobalTheory.CompanionTheory.Ar.IsTanAt tX.G z v →
        (∀ a, v ≫ tX.act.act a = sc z (algebraMap c.F S (embK c τ a)) ≫ v) →
        ∃ cf : Fin (Dw.mult τ) → S, v = (List.ofFn fun i => sc z (cf i) ≫ ub i).prod := by
  obtain ⟨C1, h1⟩ := exists_corr (a₁ := tX.act.act) (a₂ := Y.t.act.act) m.cart m.act hy.symm
  obtain ⟨C2, h2⟩ := exists_corr (a₁ := Y.oF.t.act.act) (a₂ := Y.t.act.act) (x₁ := Small.ptF y)
    (x₂ := Small.ptY Y y) Y.m.cart Y.m.act rfl
  obtain ⟨C3, h3⟩ := exists_corr (a₁ := Y.oF.t.act.act) (a₂ := Xo.univ.t.act.act) Y.m0.cart Y.m0.act
    (Small.ptF_fst y)
  let Θ := (C3.symm.trans C2).trans C1.symm
  let u : Fin (Dw.mult τ) → (GlobalTheory.CompanionTheory.Ar.epsAt y.x ⟶ Xo.univ.t.G) := fun i =>
    CategoryTheory.Over.homMk (y.u τ i) (y.tan τ i).1
  refine ⟨fun i => Θ.e (u i), fun i => ?_, fun i => (Θ.tan _).2 (y.tan τ i).2, fun i a => ?_, fun v hv hE => ?_⟩
  · have e1 : C1.e (Θ.e (u i)) = C2.e (C3.e.symm (u i)) := C1.e.apply_symm_apply _
    have e2 : (C3.e.symm (u i)).left = Small.tanF Y y τ i := by
      refine Small.eq_tanF Y y τ i _ ?_ (CategoryTheory.Over.w _)
      exact (h3 _).symm.trans (congrArg (fun q => q.left) (C3.e.apply_symm_apply (u i)))
    refine (h1 _).symm.trans ?_
    rw [e1, h2, e2]
    rfl
  · rw [← Θ.act, ← Θ.scale]
    exact congrArg Θ.e (CategoryTheory.Over.OverMorphism.ext (y.eig τ i a))
  · obtain ⟨p, rfl⟩ := Θ.e.surjective v
    have hp : Formalism.L2.Pj.IsTanAt y.x p.left := ⟨CategoryTheory.Over.w p, (Θ.tan p).1 hv⟩
    have hpE : Formalism.L2.Pj.IsEigAt c τ (Xo := Xo) p.left := fun a => by
      have e := hE a
      rw [← Θ.act, ← Θ.scale] at e
      exact congrArg (fun q => q.left) (Θ.e.injective e)
    obtain ⟨cf, ⟨U, hU, hp'⟩, -⟩ := y.basis τ _ hp hpE
    have e1 : p = (List.ofFn U).prod := CategoryTheory.Over.OverMorphism.ext hp'.symm
    refine ⟨cf, ?_⟩
    rw [e1, map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    refine Eq.trans ?_ (Θ.scale (cf i) (u i))
    exact congrArg Θ.e (CategoryTheory.Over.OverMorphism.ext (hU i))

end ModelDimension.Tan

