import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.IsometryLinkageAtSplitPrime
import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.MemLamOfIff

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

theorem discrNe (D : D7) : DiscrNe D := by
  intro cc hcc
  obtain ⟨L, hL⟩ := Formalism.L2.PairingIndexBounds.Rec.exists_pp D cc hcc
  have h4 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L hL 2 (by norm_num)
  have h6 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L hL 3 (by norm_num)
  have := Formalism.L2.Th1.F.discNeZero L
  unfold Formalism.MainNotions.TaylorLogMetric.discr Formalism.MainNotions.TaylorLogMetric.g2 Formalism.MainNotions.TaylorLogMetric.g3
  rw [h4, h6]
  simpa [PeriodPair.g₂, PeriodPair.g₃] using this

def LinkDeltaNe : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0

def LinkBaseRec : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → Nonempty (Base D cc δ)

def LinkQInt : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, B.QIntAll

def LinkEqBase : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ, IsChi D χ → ∀ N N' L L', admitted D N N' L L' →
      (B.eNat χ N N' L L' = fun z => χ (detId D (Formalism.MainNotions.StandardLatticesGL3.stdL D N') L') ^ (-((N / 2 : ℕ) : ℤ)) *
        Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) (La D (tor0 D cc δ) L L')
          (B.eNat χ N N' L (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) z) ∧
      (B.eNat χ N N' L (Formalism.MainNotions.StandardLatticesGL3.stdL D N') = fun z => χ (detId D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) L) ^ (((N' / 2 : ℕ) : ℤ)) *
        Iop D (tor0 D cc δ) (La D (tor0 D cc δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N'))
          (La D (tor0 D cc δ) L (Formalism.MainNotions.StandardLatticesGL3.stdL D N'))
          (B.eNat χ N N' (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) z) ∧
      B.eNat χ N N' (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') = B.thZero N N'

def LinkPart : Prop :=
  ∀ D : D7, AdmittedStatements D → ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    (∃ χ, IsChi D χ) ∧ ∀ χ, IsChi D χ → ∃ e : FamE D,
      NonzeroThetaVectorFamily D (tor0 D cc δ) e ∧ ThetaNormIndependent D (tor0 D cc δ) e ∧ th22U D (tor0 D cc δ) e

def LinkThetaFamily : Prop :=
  ∀ (D : D7) (C : ℝ), AdmittedStatements D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)) →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C

def LinkThetaFamily' : Prop :=
  LinkPer → ∀ (D : D7) (C : ℝ), AdmittedStatements D →
    KroneckerLimit → Uniformization → CMTransitive D → DedekindFactor D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C

def PerAll (D : D7) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)

def RestAll (D : D7) (C : ℝ) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ

def LinkThetaStatementFamily : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps) (C : ℝ),
    (∀ x (i : Fm.Ix x), PerAll (Fm.D x i)) → (∀ x (i : Fm.Ix x), RestAll (Fm.D x i) C) → StatementFamilyConstant Fm C

theorem delta_nonzero_link : LinkDeltaNe := by
  intro D cc hcc δ hδ e
  apply discrNe D cc hcc.1
  rw [← (show δ ^ 12 = discr (lamOf D cc 1) from hδ), e]
  norm_num


theorem rational_integrality_link : LinkQInt := by
  intro D cc hcc δ hδ B N N' L L' hA x hx
  obtain ⟨a, b, hab, e⟩ := hermitian_form_integral_values D cc hcc δ hδ (delta_nonzero_link D cc hcc δ hδ) N N' L L' hA x hx x hx
  have hs := IO.sqrt_d_pos D
  have hreal : (Formalism.MainNotions.TaylorLogMetric.Hf D (tor0 D cc δ) x x).im = 0 := by
    have h1 := IO.Hf_herm (tor0 D cc δ) x x
    have h2 := congrArg Complex.im h1
    rw [Complex.conj_im] at h2
    linarith
  have hb : b = 0 := by
    rw [e] at hreal
    simp at hreal
    exact hreal
  subst hb
  obtain ⟨j, hj⟩ := hab
  refine ⟨j, ?_⟩
  show Real.sqrt D.host.d / 2 * (Formalism.MainNotions.TaylorLogMetric.Hf D (tor0 D cc δ) x x).re = (j : ℝ)
  rw [e]
  have ha : (a : ℝ) = 2 * j := by
    have : a = 2 * j := by linarith
    exact_mod_cast this
  simp only [Int.cast_zero, zero_mul, add_zero, Complex.ofReal_re]
  rw [ha]
  field_simp






end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
