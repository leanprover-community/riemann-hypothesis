module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CanonB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.DualLiftInjective
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.DualLiftCompJetSub

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Chart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.Canon
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]

def pj (m : ℕ) (f : MvPowerSeries σ R) : JetR R σ m := Ideal.Quotient.mk _ (truncTotal (m + 1) f)

theorem pj_eq_mk {m : ℕ} {f : MvPowerSeries σ R} {q : MvPolynomial σ R} :
    pj m f = Ideal.Quotient.mk _ q ↔ ∀ e : σ →₀ ℕ, e.degree < m + 1 → coeff e f = q.coeff e := by
  rw [pj, Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff']
  exact forall₂_congr fun e he => by rw [MvPolynomial.coeff_sub, coeff_truncTotal _ he, sub_eq_zero]

theorem aug_pj (m : ℕ) (f : MvPowerSeries σ R) : jetAug R σ m (pj m f) = constantCoeff f := by
  show MvPolynomial.aeval (fun _ : σ => (0 : R)) (truncTotal (m + 1) f) = _
  rw [MvPolynomial.aeval_zero', MvPolynomial.constantCoeff_eq, coeff_truncTotal _ (by simp)]; rfl

theorem pj_ext {f g : MvPowerSeries σ R} (h : ∀ m, pj m f = pj m g) : f = g := by
  ext e
  exact (pj_eq_mk.1 (h e.degree) e (Nat.lt_succ_self _)).trans (coeff_truncTotal _ (Nat.lt_succ_self _))

def jS {κ : Type} (m : ℕ) (a : κ → MvPowerSeries τ R) (ha : ∀ s, constantCoeff (a s) = 0) : JetR R κ m →ₐ[R] JetR R τ m :=
  jetLift R (RingHom.ker (jetAug R τ m)) (ker_jetAug_pow τ m) (fun s => pj m (a s)) fun s => (aug_pj m _).trans (ha s)

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) {n l : ℕ}

def jP (m : ℕ) (p : Q R d n) : JetR R (Fin d) m →ₐ[R] JetR R (Fin n × Fin d) m := jS m p.1 p.2

def ptJ (m : ℕ) (p : Q R d n) : sp (R₀ := R) (JetR R (Fin n × Fin d) m) ⟶ G := spMap (jP m p) ≫ x m

def jQ (m : ℕ) (b : Fin n → Q R d l) : JetR R (Fin n × Fin d) m →ₐ[R] JetR R (Fin l × Fin d) m :=
  jS m (fun s => (b s.1).1 s.2) fun s => (b s.1).2 s.2

variable {x} (hx : IsUnivChart G d x)
include hx

theorem comb_single {v : Fin d → (Geo.Tor.epsR R ⟶ G)} (hv : ∀ j, v j = spMap (dualLift (Pi.single j 1)) ≫ x 1) (i : Fin d) :
    Geo.Tor.IsLieComb (Pi.single i 1) v (v i) := by
  have ht : ∀ j, IsTan (v j) := fun j => hv j ▸ isTan_dualLift hx _
  obtain ⟨h, e⟩ := prodPts_tan hx (Pi.single i 1) v ht
  refine (isLieComb_iff _ _ _).2 (tan_ext hx (ht i) h ?_)
  rw [e, Finset.sum_congr rfl fun j _ => congrArg _ (tcoord_eq hx _ (ht j) _ (hv j)), sum_single, tcoord_eq hx _ (ht i) _ (hv i)]

end ReciprocityTheory.ChartRestriction.G.Chart
