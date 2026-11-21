import Formalism.EllipticTorsion.Statement
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero

noncomputable section

open PowerSeries

universe u

namespace Formalism.ELL.PadicMultiplication

open Formalism.G Formalism.G.LogP

section Ring

variable {R : Type*} [CommRing R]

def mulN (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | m + 1 => MvPowerSeries.subst (![mulN F m, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R)
      F.toPowerSeries

theorem mulN_zero (F : FormalGroup R) : mulN F 0 = 0 := rfl

theorem mulN_succ (F : FormalGroup R) (m : ℕ) :
    mulN F (m + 1) = MvPowerSeries.subst
      (![mulN F m, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries := rfl

theorem constantCoeff_mulN (F : FormalGroup R) (m : ℕ) :
    MvPowerSeries.constantCoeff (mulN F m) = 0 := by
  induction m with
  | zero => simp [mulN_zero]
  | succ m ih =>
    rw [mulN_succ]
    have := constantCoeff_subst_of_zero (R := R) F.toPowerSeries
      (b := (![mulN F m, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R))
      (fun i => by fin_cases i; exacts [ih, PowerSeries.constantCoeff_X])
    rw [F.zero_constantCoeff] at this
    exact this

end Ring

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem map_mulN (F : FormalGroup (unitBall K)) (m : ℕ) :
    (mulN F (m + 1)).map (unitBall K).subtype =
      MvPowerSeries.subst
        (![(mulN F m).map (unitBall K).subtype, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K)
        (F.map (unitBall K).subtype).toPowerSeries := by
  rw [mulN_succ]
  have hs := hs2 (R := unitBall K) (constantCoeff_mulN F m)
    (u := mulN F m) (v := (PowerSeries.X : PowerSeries (unitBall K))) PowerSeries.constantCoeff_X
  rw [PowerSeries.map, MvPowerSeries.map_subst hs]
  simp only [FormalGroup.map_toPowerSeries]
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact PowerSeries.map_X _


end Formalism.ELL.PadicMultiplication

namespace Formalism.ELL.PadicMultiplication

open Formalism.G Formalism.G.LogP

variable {K : Type u} [NormedField K] [IsUltrametricDist K]



def coeffPoly (l e : PowerSeries K) (n : ℕ) : Polynomial K :=
  ∑ d ∈ Finset.range (n + 1),
    Polynomial.C (coeff d e * coeff n (l ^ d)) * Polynomial.X ^ d


end Formalism.ELL.PadicMultiplication

namespace Formalism.ELL

open Formalism.G Formalism.ELL.PadicMultiplication


end Formalism.ELL
