module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
public import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DegreeOneStatement
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.LinEig

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Jet

variable {S : Type} [CommRing S] {κ : Type}

def tanV (v : κ → S) : Jet S κ (0 + 1) →ₐ[S] DualNumber S :=
  liftJet (MvPolynomial.aeval fun i => v i • (DualNumber.eps : DualNumber S)) (by
    apply le_bot_iff.1
    have h1 : Ideal.span (Set.range fun i =>
        (MvPolynomial.aeval fun i => v i • (DualNumber.eps : DualNumber S)) (MvPolynomial.X i : MvPolynomial κ S))
        ≤ Ideal.span {(DualNumber.eps : DualNumber S)} := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [MvPolynomial.aeval_X, SetLike.mem_coe]
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    refine (Ideal.pow_right_mono h1 _).trans ?_
    rw [Ideal.span_singleton_pow]
    simp)

theorem tanV_mk (v : κ → S) (P : MvPolynomial κ S) :
    tanV v (Ideal.Quotient.mk _ P) = MvPolynomial.aeval (fun i => v i • (DualNumber.eps : DualNumber S)) P := rfl

theorem aeval_tan [Fintype κ] [DecidableEq κ] (v : κ → S) (P : MvPolynomial κ S) :
    MvPolynomial.aeval (fun i => v i • (DualNumber.eps : DualNumber S)) P =
      algebraMap S (DualNumber S) (MvPolynomial.constantCoeff P) +
        (∑ i, AddMonoidAlgebra.coeff P (Finsupp.single i 1) * v i) • (DualNumber.eps : DualNumber S) :=
  _root_.GlobalTheory.EigDir.aeval_tan v P

theorem tanV_comp_jetMap {κ' : Type} [Fintype κ'] [DecidableEq κ'] (φ : κ → MvPolynomial κ' S)
    (hφ : ∀ i, φ i ∈ orig S κ') (v : κ' → S) :
    (tanV v).comp (jetMap φ hφ : Jet S κ (0 + 1) →ₐ[S] Jet S κ' (0 + 1)) =
      tanV (fun i => ∑ j, AddMonoidAlgebra.coeff (φ i) (Finsupp.single j 1) * v j) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  show tanV v ((jetMap φ hφ : Jet S κ (0 + 1) →ₐ[S] Jet S κ' (0 + 1)) (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
    tanV _ (Ideal.Quotient.mk _ (MvPolynomial.X i))
  have e : (jetMap φ hφ : Jet S κ (0 + 1) →ₐ[S] Jet S κ' (0 + 1)) (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      Ideal.Quotient.mk _ (φ i) := by
    show Ideal.Quotient.mk _ (MvPolynomial.aeval φ (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
  rw [e, tanV_mk, tanV_mk, aeval_tan, MvPolynomial.aeval_X, GlobalTheory.EigDir.const_of_mem_orig (hφ i), map_zero, zero_add]

theorem coeff_psTrunc' {ιt : Type} [Fintype ιt] [DecidableEq ιt] (m : ℕ) (f : MvPowerSeries ιt S) (e : ιt →₀ ℕ)
    (he : e.degree ≤ m) : AddMonoidAlgebra.coeff (psTrunc m f) e = MvPowerSeries.coeff e f := by
  have hmem : e ∈ degLE m := by
    rw [degLE, Finset.mem_filter, Finset.mem_image]
    refine ⟨⟨fun i => ⟨e i, Nat.lt_succ_of_le ((Finsupp.le_degree i e).trans he)⟩, Finset.mem_univ _, ?_⟩, ?_⟩
    · ext i
      simp
    · rw [Finsupp.degree_apply] at he
      exact he
  rw [psTrunc, MvPolynomial.coeff_sum, Finset.sum_eq_single e]
  · simp [MvPolynomial.coeff_monomial]
  · intro b _ hb
    rw [MvPolynomial.coeff_monomial, if_neg hb]
  · intro h
    exact absurd hmem h

end Jet

section Law

variable {S : Type} [CommRing S] {d : ℕ}

open MvPowerSeries Formalism.FG.SolveVAux in
alias coeff_single_subst' := _root_.UpperTheory.Reformulated.B.LinearTermOfSubstitution.main

theorem law_coeff (G : Germ.FGLaw S d) (i j : Fin d) (k : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single (k, j) 1) (G.F i) = if j = i then 1 else 0 := by
  apply GlobalTheory.EigDir.law_coeff

end Law

section Pts

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {d : ℕ}
variable (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)

def Tv (v : Fin 1 × Fin d → S) : overAt y.x (DualNumber S) ⟶ Xo.univ.t.G :=
  homAt y.x (tanV v : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1

theorem tanV_smul {κ : Type} (a : S) (v : κ → S) :
    (tm (a • (LinearMap.id : S →ₗ[S] S))).comp (tanV v : Jet S κ (0 + 1) →ₐ[S] DualNumber S) = tanV (a • v) :=
  _root_.GlobalTheory.EigDir.tanV_smul a v

theorem tanV_zero {κ : Type} :
    (tanV (0 : κ → S) : Jet S κ (0 + 1) →ₐ[S] DualNumber S) =
      (Algebra.ofId S (DualNumber S)).comp (jetAug : Jet S κ (0 + 1) →ₐ[S] S) :=
  _root_.GlobalTheory.EigDir.tanV_zero

theorem jetTan_eq {κ : Type} [DecidableEq κ] (ℓ : κ) :
    (jetTan ℓ : Jet S κ (0 + 1) →ₐ[S] DualNumber S) = tanV (Pi.single ℓ 1) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  show (MvPolynomial.aeval fun i => if i = ℓ then (DualNumber.eps : DualNumber S) else 0) (MvPolynomial.X i) =
    tanV (Pi.single ℓ 1) (Ideal.Quotient.mk _ (MvPolynomial.X i))
  rw [tanV_mk, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  by_cases h : i = ℓ
  · subst h; simp
  · simp [h]

variable {y x}

end Pts

section Pts2

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} {d : ℕ}
variable {x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G}

def Dt (y : FrPt Xo c S) (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) (j : Fin d) :
    overAt y.x (DualNumber S) ⟶ Xo.univ.t.G :=
  homAt y.x (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1

end Pts2

section Main

attribute [local instance] Over.cartesianMonoidalCategory

theorem linEig_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (S : Type) [CommRing S] [Algebra c.F S]
    [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (a : 𝓞 E) (ℓ : Lt1 Dw) (i : Fin C.d),
    ∑ j, ReciprocityTheory.ChartRestriction.G.TB.dLin (C.B.A.act a) i j * C.uvec ℓ j = algebraMap c.F S (embK c ℓ.1 a) * C.uvec ℓ i := by
  apply GlobalTheory.EigDir.linEig_holds

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1.LinEig
