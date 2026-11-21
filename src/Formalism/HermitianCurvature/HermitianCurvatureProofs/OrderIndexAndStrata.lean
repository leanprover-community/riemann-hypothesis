import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointwiseStabiliserParametrisationBijective

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.OrderIndexAndStrata

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni)
open Formalism.FourierDecayAlt.S3

noncomputable def tb : MassData Unit where
  g := fun _ => 5
  glk := fun _ => 6
  uk := fun _ => 2
  nn := fun _ => 4
  gg := fun _ => 48
  μKp := fun _ => 6
  μKnatp := fun _ => 3
  μKppp := fun _ => 1
  μSp := fun _ => 3
  μSp' := fun _ => 6
  μSppp := fun _ => 1
  μSppp' := fun _ => 2
  Mp := fun _ => 1
  localVolumeAtPlace := fun _ => 1
  μKo := 2
  μSo := 1
  μSo' := 1
  Mo := 4
  localVolumeArchimedean := 1
  μH := 6
  μH' := 6
  μHpp := 2
  μHpp' := 2
  μN := 1/2
  μN' := 1
  volZZ := 1
  volPP := 1
  al := 1
  volG := 6
  volHa := 2
  volHa' := 3
  volNa := 1
  volNa' := 1
  volB := 1
  volH := 1
  volH' := 1
  volN := 2
  volN' := 1
  Coo := 1
  deg := 1
  dimπ := 1
  dimπ' := 1
  ρ0 := 1/3
  ρ0' := 1/2
  d := 1
  d' := 3/2
  n0c := 1
  supdens := 1
  e1 := 1
  δ := 0
  Kgs2 := 4/5
  KV := 1/2
  Sig := 1/6
  KtopV := 1/2
  IntN := 1
  IntC := 1
  IntOO := 1








theorem det_mid {A : Type} [CommRing A] {r k : ℕ} (x : Matrix (Idx r k) (Idx r k) A) (hx : IsUnit x.det)
    (h21 : b21 x = 0) (h31 : b31 x = 0) (h32 : b32 x = 0) : IsUnit (b22 x).det := by
  have e21 : ∀ i j, x (Sum.inr (Sum.inl i)) (Sum.inl j) = 0 := fun i j => by
    simpa [b21] using congrFun (congrFun h21 i) j
  have e31 : ∀ i j, x (Sum.inr (Sum.inr i)) (Sum.inl j) = 0 := fun i j => by
    simpa [b31] using congrFun (congrFun h31 i) j
  have e32 : ∀ i j, x (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) = 0 := fun i j => by
    simpa [b32] using congrFun (congrFun h32 i) j
  have hx' : x = Matrix.fromBlocks (b11 x) (Matrix.fromCols (b12 x) (b13 x)) 0
      (Matrix.fromBlocks (b22 x) (b23 x) 0 (b33 x)) := by
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j <;>
      simp [b11, b12, b13, b22, b23, b33, e21, e31, e32]
  have hdet : x.det = (b11 x).det * ((b22 x).det * (b33 x).det) := by
    conv_lhs => rw [hx']
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁]
  rw [hdet] at hx
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right hx)

theorem mid_form {A : Type} [CommRing A] {k : ℕ} (y : Matrix (Mid k) (Mid k) A) (hy : IsUnit y.det)
    (c22 : ∀ a, y a (Sum.inr ()) = if a = Sum.inr () then 1 else 0)
    (r22 : ∀ b, y (Sum.inr ()) b = if b = Sum.inr () then 1 else 0) :
    ∃ h, IsUnit h.det ∧ y = midEmb h := by
  have hy' : y = midEmb (Matrix.of fun a b => y (Sum.inl a) (Sum.inl b)) := by
    ext (a | ⟨⟩) (b | ⟨⟩)
    · simp [midEmb]
    · simpa [midEmb] using c22 (Sum.inl a)
    · simpa [midEmb] using r22 (Sum.inl b)
    · simpa [midEmb] using c22 (Sum.inr ())
  refine ⟨_, ?_, hy'⟩
  rw [hy', Formalism.FourierDecayAlt.P.S3x1.midEmb_det] at hy
  exact hy

theorem sFrame (hS : SExplicit) : SIsFrameStabiliser := by
  intro A _ r k x hx
  rw [hS]
  constructor
  · rintro ⟨h11, h33, h21, h31, h32, h, hh, h22⟩
    refine ⟨⟨h11, h21, h31, fun a => ?_, fun a => ?_⟩, ⟨h33, h32, fun b => ?_, fun b => ?_⟩⟩
    · rw [h22]; rcases a with a | ⟨⟩ <;> simp [midEmb]
    · simp [h32]
    · rw [h22]; rcases b with b | ⟨⟩ <;> simp [midEmb]
    · simp [h21]
  · rintro ⟨⟨h11, h21, h31, hc, -⟩, ⟨h33, h32, hr, -⟩⟩
    obtain ⟨h, hh, he⟩ := mid_form (b22 x) (det_mid x hx h21 h31 h32) hc hr
    exact ⟨h11, h33, h21, h31, h32, h, hh, he⟩



end Formalism.FourierDecayAlt.P.OrderIndexAndStrata








