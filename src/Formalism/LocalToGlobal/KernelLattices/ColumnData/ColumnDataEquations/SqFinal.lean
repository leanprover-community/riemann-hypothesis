import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitTripleEquations.MuOneOfSplit
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.RightMoveTrianglesOfUnit
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SecondConstantHolds

section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.Sq

open Formalism.L2.PairingIndexBounds.Eq.Sq Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

section Gen

variable {V : Type} [AddCommGroup V] [Module ℂ V]

structure PolFam (H : Sesq V) (α : V → ℂ) {ι : Type} (Y : ι → AddSubgroup V) (A A' : AddSubgroup V) : Prop where
  meet : ∀ x, x ∈ A → x ∈ A' → ∀ i, x ∈ Y i
  dec : ∀ i, ∀ x ∈ Y i, ∃ a ∈ A, ∃ b ∈ A', a ∈ Y i ∧ b ∈ Y i ∧ x = a + b
  semiA : ∀ x y, x ∈ A → y ∈ A → ∀ i j k, x ∈ Y i → y ∈ Y j → x + y ∈ Y k →
    α (x + y) = α x * α y * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ))
  semiA' : ∀ x y, x ∈ A' → y ∈ A' → ∀ i j k, x ∈ Y i → y ∈ Y j → x + y ∈ Y k →
    α (x + y) = α x * α y * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ))

theorem psiT_one {H : Sesq V} {α : V → ℂ} {Λ₂ Λ₃ : AddSubgroup V} (h2 : IsSemiChar H Λ₂ α) (h3 : IsSemiChar H Λ₃ α)
    {z y : V} (hz : z ∈ Λ₃) (hy : y ∈ Λ₂)
    (hlaw : α (z + y) = α z * α y * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H z y : ℂ))) :
    psiT H α z y = 1 := by
  have hz2 : α z * α z = 1 := by rcases h3.1 z hz with h | h <;> rw [h] <;> norm_num
  have hy2 : α y * α y = 1 := by rcases h2.1 y hy with h | h <;> rw [h] <;> norm_num
  have he : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H z y : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H z y : ℂ)) = 1 := by
    rw [← Complex.exp_add, show (Real.pi : ℂ) * Complex.I * (altE H z y : ℂ) +
      -(Real.pi : ℂ) * Complex.I * (altE H z y : ℂ) = 0 by ring, Complex.exp_zero]
  unfold psiT
  rw [hlaw]
  calc _ = (α z * α z) * (α y * α y) * (Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H z y : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H z y : ℂ))) := by ring
    _ = 1 := by rw [hz2, hy2, he]; ring

theorem splitTri_of {H : Sesq V} {α : V → ℂ} {ι : Type} {Y : ι → AddSubgroup V} {A A' : AddSubgroup V}
    (hP : PolFam H α Y A A') (i₁ i₂ i₃ : ι) (hT : TripleData H α (Y i₁) (Y i₂) (Y i₃)) :
    SplitTri H α (Y i₁) (Y i₂) (Y i₃) A A' where
  meet x h h' := ⟨hP.meet x h h' i₁, hP.meet x h h' i₂, hP.meet x h h' i₃⟩
  dec₁ := hP.dec i₁
  dec₂ := hP.dec i₂
  dec₃ := hP.dec i₃
  isoA z y hz hy hz3 hy2 h1 := psiT_one hT.sc₂ hT.sc₃ hz3 hy2 (hP.semiA z y hz hy i₃ i₂ i₁ hz3 hy2 h1)
  isoA' z y hz hy hz3 hy2 h1 := psiT_one hT.sc₂ hT.sc₃ hz3 hy2 (hP.semiA' z y hz hy i₃ i₂ i₁ hz3 hy2 h1)

end Gen

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def sqFam (T : TaylorLogMetric.Tor D) {N N' : ℕ} (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Bool × Bool → AddSubgroup (TaylorLogMetric.VC D N N') :=
  fun p => TaylorLogMetric.La D T (if p.1 then L₁ else L) (if p.2 then L'' else L')

def SqSplit (B : Cd.Base D cc δ) : Prop :=
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    Even N → Even N' → SD D L → SD D L₁ → SD D L' → SD D L'' →
    ∃ A A' : AddSubgroup (TaylorLogMetric.VC D N N'),
      PolFam (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor) (sqFam B.tor L L₁ L' L'') A A'

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.Sq
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.Sq

open Formalism.L2.PairingIndexBounds.Eq.Sq Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem sqP_of {B : Cd.Base D cc δ} (hL : B.LatAll) (hS : SqSplit B) : SqP D B.tor := by
  intro N N' L L₁ L' L'' hN hN' h1 h2 h3 h4 G hG
  obtain ⟨A, A', hP⟩ := hS N N' L L₁ L' L'' hN hN' h1 h2 h3 h4
  by_cases hG0 : G = 0
  · subst hG0
    funext v
    simp [TaylorLogMetric.Iop, TaylorLogMetric.U]
  have hF : ∃ F ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor L L'), F ≠ 0 := ⟨G, fun x hx z => hG.2 x hx z, hG0⟩
  have hT1 := tripleData_of hL (admissible_of_integral_conj_le hN hN' h1 h3) (admissible_of_integral_conj_le hN hN' h2 h3) (admissible_of_integral_conj_le hN hN' h2 h4)
  have hT2 := tripleData_of hL (admissible_of_integral_conj_le hN hN' h1 h3) (admissible_of_integral_conj_le hN hN' h1 h4) (admissible_of_integral_conj_le hN hN' h2 h4)
  obtain ⟨S₂, S₃, hS₂, hS₃, hμ⟩ :=
    mu_one_of_split hT1 (splitTri_of hP (false, false) (true, false) (true, true) hT1) hF
  obtain ⟨T₂, T₃, hT₂, hT₃, hν⟩ :=
    mu_one_of_split hT2 (splitTri_of hP (false, false) (false, true) (true, true) hT2) hF
  funext v
  have e1 := tripleFormula _ _ _ _ _ _ hT1 S₂ S₃ hS₂ hS₃ G (fun x hx z => hG.2 x hx z) v
  have e2 := tripleFormula _ _ _ _ _ _ hT2 T₂ T₃ hT₂ hT₃ G (fun x hx z => hG.2 x hx z) v
  rw [hμ, one_mul] at e1
  rw [hν, one_mul] at e2
  exact e1.trans e2.symm

theorem eqP_of_split (B : Cd.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ)
    (hSp : SqSplit B) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) : B.EqP χ :=
  J.eqP_of_paths B hcc hδ hδ0 hS χ hχ (sqP_of (B.latAll hcc hδ hδ0) hSp) hTL hTR

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.Sq
end
end
