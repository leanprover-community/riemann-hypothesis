import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TensorAlgebraicallyClosedDomain
import BuildAid.ForwardExisting

section
open TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isDomain_tensor_of_algebraically_closed_constants :
    ∀ (K Ω C : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Field C] [Algebra K C],
      (∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) → IsDomain (Ω ⊗[K] C) :=
  @PositivityTheory.Xgn.tensor_algebraically_closed_domain

end GlobalTheory.CompanionTheory.Ar.Flat
end

open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alg_closed_tensor_isDomain : ∀ (K Ω C : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Field C] [Algebra K C], (∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) → IsDomain (Ω ⊗[K] C) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.isDomain_tensor_of_algebraically_closed_constants
