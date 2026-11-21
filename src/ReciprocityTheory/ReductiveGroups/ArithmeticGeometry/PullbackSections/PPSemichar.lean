import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Semichar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnHolFamOfHolTo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj MonObj
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem hermForm_zero_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) : hermForm Hm 0 w = 0 := by
  unfold hermForm
  simp

theorem hermForm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  unfold hermForm
  rw [add_dotProduct]

theorem hermForm_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  unfold hermForm
  rw [star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  unfold hermForm
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hji : star (Hm i j) = Hm j i := by
    have := congrFun (congrFun hH j) i
    rwa [Matrix.conjTranspose_apply] at this
  simp only [Pi.star_apply, star_star, hji]
  ring

theorem hermForm_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (t • z) w = t * hermForm Hm z w := by
  unfold hermForm
  rw [smul_dotProduct, smul_eq_mul]

theorem hermForm_real_smul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm z ((t : ℂ) • w) = t * hermForm Hm z w := by
  unfold hermForm
  have h1 : star ((t : ℂ) • w) = (t : ℂ) • star w := by
    ext i
    simp [Complex.conj_ofReal]
  rw [h1, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

def mulTy {g : ℕ} (ty : Fin g → E →+* ℂ) (a : 𝓞 E) (z : Fin g → ℂ) : Fin g → ℂ := fun i => ty i (a : E) * z i

theorem mulTy_zero {g : ℕ} (ty : Fin g → E →+* ℂ) (a : 𝓞 E) : mulTy ty a 0 = 0 := by
  funext i
  simp [mulTy]

theorem mulTy_add {g : ℕ} (ty : Fin g → E →+* ℂ) (a : 𝓞 E) (z z' : Fin g → ℂ) :
    mulTy ty a (z + z') = mulTy ty a z + mulTy ty a z' := by
  funext i
  simp [mulTy, mul_add]

theorem mulTy_smul {g : ℕ} (ty : Fin g → E →+* ℂ) (a : 𝓞 E) (t : ℂ) (z : Fin g → ℂ) :
    mulTy ty a (t • z) = t • mulTy ty a z := by
  funext i
  simp only [mulTy, Pi.smul_apply, smul_eq_mul]
  ring

theorem herm_adj {D : Datum H} {g : ℕ} {ty : Fin g → E →+* ℂ} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    {Hm : Matrix (Fin g) (Fin g) ℂ} (hIm : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) (a : 𝓞 E)
    (z w : Fin g → ℂ) : hermForm Hm (mulTy ty a z) w = hermForm Hm z (mulTy ty (H.bar a) w) := by
  obtain ⟨hsm, -, -, hspan, -⟩ := hP
  have hA : ∀ x, P (a • x) = mulTy ty a (P x) := fun x => funext fun i => by rw [hsm]; rfl
  have hB : ∀ x, P (H.bar a • x) = mulTy ty (H.bar a) (P x) := fun x => funext fun i => by rw [hsm]; rfl
  have hsr : ∀ (t : ℝ) (v : Fin g → ℂ), t • v = (t : ℂ) • v := fun t v => by
    ext i
    simp [Complex.real_smul]

  have step1 : ∀ y v, (hermForm Hm (mulTy ty a v) (P y)).im =
      (hermForm Hm v (mulTy ty (H.bar a) (P y))).im := by
    intro y
    let S : Submodule ℝ (Fin g → ℂ) :=
      { carrier := {v | (hermForm Hm (mulTy ty a v) (P y)).im =
          (hermForm Hm v (mulTy ty (H.bar a) (P y))).im}
        add_mem' := by
          intro v v' hv hv'
          simp only [Set.mem_setOf_eq] at *
          rw [mulTy_add, hermForm_add_left, hermForm_add_left, Complex.add_im, Complex.add_im, hv, hv']
        zero_mem' := by
          simp only [Set.mem_setOf_eq, mulTy_zero, hermForm_zero_left]
        smul_mem' := by
          intro t v hv
          simp only [Set.mem_setOf_eq] at *
          rw [hsr, mulTy_smul, hermForm_smul_left, hermForm_smul_left, Complex.im_ofReal_mul,
            Complex.im_ofReal_mul, hv] }
    have hle : Submodule.span ℝ (Set.range P) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      show (hermForm Hm (mulTy ty a (P x)) (P y)).im = (hermForm Hm (P x) (mulTy ty (H.bar a) (P y))).im
      rw [← hA, ← hB, hIm, hIm, D.adj]
    rw [hspan] at hle
    exact fun v => hle Submodule.mem_top
  have key : ∀ u v, (hermForm Hm (mulTy ty a u) v).im = (hermForm Hm u (mulTy ty (H.bar a) v)).im := by
    intro u
    let S : Submodule ℝ (Fin g → ℂ) :=
      { carrier := {v | (hermForm Hm (mulTy ty a u) v).im = (hermForm Hm u (mulTy ty (H.bar a) v)).im}
        add_mem' := by
          intro v v' hv hv'
          simp only [Set.mem_setOf_eq] at *
          rw [mulTy_add, hermForm_add_right, hermForm_add_right, Complex.add_im, Complex.add_im, hv, hv']
        zero_mem' := by
          simp only [Set.mem_setOf_eq, mulTy_zero]
          unfold hermForm
          simp
        smul_mem' := by
          intro t v hv
          simp only [Set.mem_setOf_eq] at *
          rw [hsr, mulTy_smul, hermForm_real_smul_right, hermForm_real_smul_right, Complex.im_ofReal_mul,
            Complex.im_ofReal_mul, hv] }
    have hle : Submodule.span ℝ (Set.range P) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      exact step1 y u
    rw [hspan] at hle
    exact fun v => hle Submodule.mem_top
  have hI : ∀ u v, (hermForm Hm u v).re = (hermForm Hm (Complex.I • u) v).im := by
    intro u v
    rw [hermForm_smul_left]
    simp
  apply Complex.ext
  · rw [hI, hI, ← mulTy_smul]
    exact key _ _
  · exact key z w


section Prim

variable {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x)

def qW (z : Fin W.g → ℂ) : Sp ℂ ⟶ Xo.univ.t.G.left := (W.F.ex (W.ik k) W.Pm z).left

def tyW' : Fin W.g → E →+* ℂ := fun j => relab c σ (W.e j).1


theorem pm_smul (b : 𝓞 E) (y : (W.F.Di (W.ik k)).La) : W.Pm (b • y) = mulTy (tyW' W) b (W.Pm y) := by
  funext i
  rw [W.per.1]
  rfl


def linI (I : Finset (Fin 2)) (z : Fin W.g → ℂ) : Fin W.g → ℂ :=
  (if (0 : Fin 2) ∈ I then z else 0) + (if (1 : Fin 2) ∈ I then mulTy (tyW' W) H.w0 z else 0)

def linB (I : Finset (Fin 2)) (b : (W.F.Di (W.ik k)).La) : (W.F.Di (W.ik k)).La :=
  (if (0 : Fin 2) ∈ I then b else 0) + (if (1 : Fin 2) ∈ I then H.w0 • b else 0)






abbrev phiP : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)) → (Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) :=
  Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφG Xo.univ.t ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0])

abbrev epsP : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)) → ℤ := Sum.elim (fun _ => 1) fun I => -cε 2 I

def linK : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)) → (Fin W.g → ℂ) → (Fin W.g → ℂ) :=
  Sum.elim (fun _ z => z) fun I z => linI W I.down z

def linBK : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)) → (W.F.Di (W.ik k)).La → (W.F.Di (W.ik k)).La :=
  Sum.elim (fun _ b => b) fun I b => linB W I.down b





end Prim

end ReciprocityTheory.ChartRestriction.G.PullbackSections
