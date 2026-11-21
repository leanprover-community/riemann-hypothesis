import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

open C2x2




lemma c2x3_iSet_card {m a : ℕ} (h : a ≤ m) : (C2.iSet m a).card = a := by
  unfold C2.iSet
  rw [Fin.card_filter_val_lt]; omega







end Formalism.FourierDecayAlt.P
