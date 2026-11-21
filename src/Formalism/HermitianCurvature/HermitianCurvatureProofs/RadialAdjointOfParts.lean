import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOrbitSet

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Exhaust : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (f : B.Mat k r → (Wq →L[ℂ] Wp)) (K : Set ((Fin r → ℂ) × ℂ)),
    Q.SmoothLev k r 0 (Q.OmPlus k r D.z D.z') f → IsEqv D (Om k r D.z D.z') f →
    IsCompact K → K ⊆ QDom k r D.z D.z' →
    (∀ q ∈ QDom k r D.z D.z', q ∉ K → f (B.gq D q) = 0) →
    ∃ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F ∧
      (∃ C : Set (B.Mat k r), IsCompact C ∧ C ⊆ Om k r D.z D.z' ∧ ∀ g, g ∉ C → F g = 0) ∧
      ∀ g ∈ Om k r D.z D.z', B.JF D F g = f g

def JThetaC : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    B.SmoothCoef (Om k r D.z D.z') Θ → B.Commutes D (Om k r D.z D.z') Θ → B.CkOn ⊤ (B.GV k r) F →
    (∃ C : Set (B.Mat k r), IsCompact C ∧ C ⊆ Om k r D.z D.z' ∧ ∀ g, g ∉ C → F g = 0) →
    ∀ g ∈ Om k r D.z D.z', B.JF D (B.opApply Θ F) g = B.opApply Θ (B.JF D F) g ∧
      B.JF D (B.opAdj Θ F) g = B.opAdj Θ (B.JF D F) g

def BetaAdjC : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (F F' : B.Mat k r → (Wq →L[ℂ] Wp)),
    B.IntFormula D → B.SmoothCoef (Om k r D.z D.z') Θ → B.Commutes D (Om k r D.z D.z') Θ →
    B.CkOn ⊤ (B.GV k r) F → B.CkOn ⊤ (B.GV k r) F' →
    (∃ C : Set (B.Mat k r), IsCompact C ∧ C ⊆ Om k r D.z D.z' ∧ ∀ g, g ∉ C → F g = 0) →
    (∃ C : Set (B.Mat k r), IsCompact C ∧ C ⊆ Om k r D.z D.z' ∧ ∀ g, g ∉ C → F' g = 0) →
    B.beta D (B.opApply Θ F) F' = B.beta D F (B.opAdj Θ F')

def RadAdjOfParts : Prop := Exhaust → JThetaC → BetaAdjC → RadAdj

variable {k r : ℕ}

theorem bcWeight_nonneg (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (sub_nonneg.2 h) _)
  · exact le_rfl

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem adj_local (Θ : DiffOp k r Wp Wq) {f₁ f₂ : Mat k r → (Wq →L[ℂ] Wp)} {V : Set (Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) : ∀ x ∈ V, x ∈ GV k r → opAdj Θ f₁ x = opAdj Θ f₂ x := by
  intro x hx hxG
  unfold opAdj
  congr 1
  refine List.map_congr_left fun T _ => ?_
  rw [PositiveOrbitOpen.rw_local (f₁ := fun y => T.coefAdj y (f₁ y)) (f₂ := fun y => T.coefAdj y (f₂ y)) hV
    (fun y hy hyG => by simp only [h y hy hyG]) T.word.reverse
    (fun X hX => T.word_lie X (List.mem_reverse.1 hX)) x hx hxG]

theorem betaBig_congr (D : RealPlaceData k r Wp Wq)
    {J₁ J₁' J₂ J₂' : Mat k r → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)}
    (h : ∀ g ∈ Om k r D.z D.z', J₁ g = J₂ g) (h' : ∀ g ∈ Om k r D.z D.z', J₁' g = J₂' g) :
    betaBig k r (Tz k r D.z) (Tz k r D.z') D.μsec J₁ J₁' = betaBig k r (Tz k r D.z) (Tz k r D.z') D.μsec J₂ J₂' := by
  unfold betaBig
  apply integral_congr_ae
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ Om k r D.z D.z' := hq hQ
    simp only [h _ hg, h' _ hg]
  · have h0 : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (bcWeight_nonneg _ _ q)
    simp only [h0, Complex.ofReal_zero, zero_mul]

end Formalism.FourierDecayAlt.P.JFxG

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


end Formalism.FourierDecayAlt.P
