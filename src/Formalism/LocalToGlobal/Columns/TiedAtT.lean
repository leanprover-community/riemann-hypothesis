module

public import Formalism.LocalToGlobal.Columns.TiedCls
public import Formalism.LocalToGlobal.Columns.AtTOwedS
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)

end Gen

section Val

variable {K : Type} [Field K] [NumberField K] (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
  (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))

include hval in
theorem att_val_pos (w : Pl.Pl) (x : 𝓞 K) : (0 : WithTop ℤ) < Pl.val w (x : K) ↔ x ∈ (pw w).asIdeal := by
  by_cases hx : x = 0
  · subst hx
    have h0 : Pl.val w (((0 : 𝓞 K) : 𝓞 K) : K) = ⊤ := by
      rw [show (((0 : 𝓞 K) : 𝓞 K) : K) = 0 from rfl]
      exact (Pl.val w).map_zero
    rw [h0]
    exact ⟨fun _ => zero_mem _, fun _ => WithTop.coe_lt_top (0 : ℤ)⟩
  · have hx' : (x : K) ≠ 0 := fun h => hx (RingOfIntegers.ext h)
    have h0 : (pw w).valuation K (x : K) ≠ 0 := (Valuation.ne_zero_iff _).2 hx'
    rw [hval w _ hx', ← (pw w).valuation_lt_one_iff_mem (K := K)]
    unfold Formalism.BasicNotions.vAdd
    rw [← WithTop.coe_zero, WithTop.coe_lt_coe, neg_pos, ← WithZero.log_one, WithZero.log_lt_log h0 one_ne_zero]

include hval in
theorem att_resChar_mem (w : Pl.Pl) : ((Pl.resChar w : ℕ) : 𝓞 K) ∈ (pw w).asIdeal := by
  rw [← att_val_pos Pl pw hval]
  have h := Pl.val_resChar w
  have e : ((((Pl.resChar w : ℕ) : 𝓞 K) : 𝓞 K) : K) = ((Pl.resChar w : ℕ) : K) := map_natCast (algebraMap (𝓞 K) K) _
  rw [e, h, ← WithTop.coe_zero, WithTop.coe_lt_coe]
  exact_mod_cast Pl.ramIdx_pos w

end Val

section Seen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)

end Seen

section Rec

variable {d : ColDat} (a : ColArgs d)

end Rec

end Formalism.L2.Col
