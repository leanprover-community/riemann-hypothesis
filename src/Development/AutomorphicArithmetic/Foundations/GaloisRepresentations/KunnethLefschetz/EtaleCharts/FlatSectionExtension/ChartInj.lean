module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private lemma appLE_univ_congr_of_eq {V Z : Scheme.{0}} {f g : V ⟶ Z} (hfg : f = g) (U : Z.Opens)
    (e : ⊤ ≤ f ⁻¹ᵁ U) (e' : ⊤ ≤ g ⁻¹ᵁ U) : f.appLE U ⊤ e = g.appLE U ⊤ e' := by
  subst hfg; rfl

private lemma appLE_lift_eq {Y V : Scheme.{0}} (C : Y.Opens) (l : V ⟶ (C : Scheme.{0}))
    (h : ⊤ ≤ (l ≫ C.ι) ⁻¹ᵁ C) : (l ≫ C.ι).appLE C ⊤ h = C.topIso.inv ≫ l.appTop := by
  rw [← Scheme.Hom.appLE_comp_appLE l C.ι C ⊤ ⊤ (by simp) (by simp), Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  simp
  congr 1

private lemma eq_of_appLE_eq {Y V : Scheme.{0}} (C : Y.Opens) (hC : IsAffineOpen C) (y y' : V ⟶ Y)
    (h : ⊤ ≤ y ⁻¹ᵁ C) (h' : ⊤ ≤ y' ⁻¹ᵁ C) (e : y.appLE C ⊤ h = y'.appLE C ⊤ h') : y = y' := by
  have r : ∀ z : V ⟶ Y, ⊤ ≤ z ⁻¹ᵁ C → Set.range z ⊆ Set.range C.ι := by
    rintro z hz _ ⟨x, rfl⟩
    simpa using hz (Set.mem_univ x)
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ C.ι = y := ⟨_, IsOpenImmersion.lift_fac C.ι y (r y h)⟩
  obtain ⟨l', rfl⟩ : ∃ l, l ≫ C.ι = y' := ⟨_, IsOpenImmersion.lift_fac C.ι y' (r y' h')⟩
  haveI : IsAffine (C : Scheme.{0}) := hC
  rw [appLE_lift_eq, appLE_lift_eq] at e
  have e2 : l.appTop = l'.appTop := (cancel_epi C.topIso.inv).mp e
  rw [ext_of_isAffine e2]

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.chartInj :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} (y y' : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c α).C k), y ≫ π = y' ≫ π → uV B α k y h = uV B α k y' h' → y = y' := by
  intro K _ W Z Y q i π D d B α k V y y' h h' hπ hu
  have hle := (B.c α).C_le k
  refine eq_of_appLE_eq _ ((B.c α).C_aff k) y y' h h' ?_
  have hpi : ∀ r : Γ(Z, B.V α), (y.appLE _ ⊤ h).hom ((π.appLE (B.V α) _ hle).hom r) =
      (y'.appLE _ ⊤ h').hom ((π.appLE (B.V α) _ hle).hom r) := by
    intro r
    have e1 := Scheme.Hom.appLE_comp_appLE y π (B.V α) ((B.c α).C k) ⊤ hle h
    have e2 := Scheme.Hom.appLE_comp_appLE y' π (B.V α) ((B.c α).C k) ⊤ hle h'
    have e3 := e1.trans ((appLE_univ_congr_of_eq hπ (B.V α) _ _).trans e2.symm)
    exact congrArg (fun t => t.hom r) e3
  have hP := MvPolynomial.ringHom_ext
    (f := (y.appLE _ ⊤ h).hom.comp (MvPolynomial.eval₂Hom (π.appLE (B.V α) _ hle).hom ((B.c α).u k)))
    (g := (y'.appLE _ ⊤ h').hom.comp (MvPolynomial.eval₂Hom (π.appLE (B.V α) _ hle).hom ((B.c α).u k)))
    (fun r => by simpa using hpi r)
    (fun m => by simpa [uV] using congrFun hu m)
  refine CommRingCat.hom_ext (RingHom.ext fun s => ?_)
  obtain ⟨P, rfl⟩ := (B.c α).surj k s
  exact congrArg (fun t => t P) hP
