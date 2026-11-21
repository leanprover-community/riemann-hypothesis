import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLiftBasis
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSkewValue

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

section

variable [Fact (IsFixF K F)]


theorem map_mk_eq_iff (𝔭 : Ideal (𝓞 F)) (k : ℕ) (M N : Matrix κ κ (𝓞 K)) :
    M.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = N.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) ↔
      ∀ i j, (M - N) i j ∈ extP K 𝔭 ^ k := by
  constructor
  · intro h i j
    exact Ideal.Quotient.eq.1 (congrFun (congrFun h i) j)
  · intro h
    ext i j
    exact Ideal.Quotient.eq.2 (h i j)




end


theorem form_mem {J : Ideal (𝓞 K)} {M : Matrix κ κ (𝓞 K)} (hM : ∀ i j, M i j ∈ J) (u v : κ → 𝓞 K) :
    u ⬝ᵥ (M *ᵥ v) ∈ J :=
  J.sum_mem fun i _ => J.mul_mem_left _ (J.sum_mem fun j _ => J.mul_mem_right _ (hM i j))


end Formalism.HermitianLattices.Ext.L3.HU
