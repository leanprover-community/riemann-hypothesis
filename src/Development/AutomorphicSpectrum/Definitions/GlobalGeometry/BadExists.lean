import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TowerOriginModel

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem chi_odd (H : Host E) :
    haveI : Fact H.d.Prime := ⟨H.d_prime⟩
    ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ)) (-1) = -1 := by
  haveI : Fact H.d.Prime := ⟨H.d_prime⟩
  have h4 : H.d % 4 = 3 := by have := H.d_mod; omega
  have h2 : ringChar (ZMod H.d) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; have := H.d_mod; omega
  rw [MulChar.ringHomComp_apply, quadraticChar_neg_one h2, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]
  simp

theorem L_ne (H : Host E) :
    haveI : Fact H.d.Prime := ⟨H.d_prime⟩
    DirichletCharacter.LFunction
      ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ H.d) 1 ≠ 0 := by
  haveI : Fact H.d.Prime := ⟨H.d_prime⟩
  haveI : NeZero H.d := ⟨H.d_prime.ne_zero⟩
  apply DirichletCharacter.LFunction_apply_one_ne_zero
  intro h
  have h1 := chi_odd (E := E) H
  rw [h, MulChar.one_apply isUnit_one.neg] at h1
  norm_num at h1



variable {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {T : Top.RootTower (CMType H) (D.p + D.q)}

theorem sig_pos (o : TowerOrigin Y T) : 1 ≤ D.p ∧ 1 ≤ D.q := by
  have h1 := T.j_pos
  have h2 := T.j_lt
  rw [o.j_eq] at h1 h2
  omega

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y' : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y' Sys}


theorem pi_pt_ne (o : RootOrigin Y' S RM Fx) (x : o.Re.R.X) :
    ∃ a : ℂ, a ≠ 0 ∧ (fun i => o.Re.R.lift x x ⟨o.k₀, o.ix i⟩) = a • Fx.pt (o.Re.π x) := by
  obtain ⟨a, ha⟩ := o.π_pt x
  refine ⟨a, ?_, ha⟩
  rintro rfl
  obtain ⟨hnz, -⟩ := o.Re.R.mem x x (o.Re.R.mem_U x)
  obtain ⟨i, hi⟩ := hnz o.k₀
  apply hi
  have h := congrFun ha (o.ix.symm i)
  simp only [Equiv.apply_symm_apply, zero_smul, Pi.zero_apply] at h
  exact h

theorem genPt_eq (o : RootOrigin Y' S RM Fx) : genPt Fx.ξf = genPt o.𝔐.ξ₀ := by
  have hsub : ∀ (K : Type) [Field K] (p q : PrimeSpectrum K), p = q := fun K _ p q =>
    PrimeSpectrum.ext ((Ideal.eq_bot_of_prime p.asIdeal).trans (Ideal.eq_bot_of_prime q.asIdeal).symm)
  have h1 := o.g_over
  have h2 := o.𝔐.fn_over
  unfold Dominates at h2
  rw [h1] at h2
  have h3 : Fx.ξf ((spMap o.g) (IsLocalRing.closedPoint RM.Ω)) =
      o.𝔐.ξ₀ ((Spec.map (CommRingCat.ofHom o.𝔐.fn)) (IsLocalRing.closedPoint RM.Ω)) :=
    congrArg (fun φ => φ (IsLocalRing.closedPoint RM.Ω)) h2
  unfold genPt
  rw [hsub Fx.Ωf (IsLocalRing.closedPoint Fx.Ωf) ((spMap o.g) (IsLocalRing.closedPoint RM.Ω)),
    hsub o.𝔐.Ω₀ (IsLocalRing.closedPoint o.𝔐.Ω₀)
      ((Spec.map (CommRingCat.ofHom o.𝔐.fn)) (IsLocalRing.closedPoint RM.Ω))]
  exact h3

end GlobalTheory.CompanionTheory.Ar.TowerOriginModel
