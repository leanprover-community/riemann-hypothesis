module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCut

@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVCrdAlg

variable {R : Type*} [Ring R]

def cont (D e : ℕ → R) (a : ℕ) : ℕ → R
  | 0 => 1
  | 1 => D a
  | n + 2 => D (a + n + 1) * cont D e a (n + 1) - e (a + n + 1) * cont D e a n

theorem cont_zero (D e : ℕ → R) (a : ℕ) : cont D e a 0 = 1 := rfl

theorem cont_one (D e : ℕ → R) (a : ℕ) : cont D e a 1 = D a := rfl

theorem cont_two (D e : ℕ → R) (a n : ℕ) :
    cont D e a (n + 2) = D (a + n + 1) * cont D e a (n + 1) - e (a + n + 1) * cont D e a n := rfl

def topK (Dt e : ℕ → R) (r : ℕ) : ℕ → R × R
  | 0 => (1, 0)
  | m + 1 => ((topK Dt e r m).1 * Dt m - e (r - m) * (topK Dt e r m).2, (topK Dt e r m).1)

def botA (D Cb Cbi : ℕ → R) (r : ℕ) : ℕ → R × R
  | 0 => (1, 0)
  | i + 1 => if i < r then
      (D i * (botA D Cb Cbi r i).1 - Cb i * (botA D Cb Cbi r i).2, Cbi i * (botA D Cb Cbi r i).1)
      else botA D Cb Cbi r i

end Formalism.FourierDecayAlt.P.CutMP.TVCrdAlg
