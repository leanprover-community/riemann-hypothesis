module

public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# The valuative criterion for integrality in a field

For a ring homomorphism into a field, integrality over its image is membership in every valuation
subring containing that image.
-/

public section

/-- An element of a field is integral over a ring map's image if and only if it belongs to every
valuation subring containing that image. -/
@[stacks 090P "part (1), for the integral closure of the image of a ring map"]
lemma RingHom.isIntegralElem_iff_forall_valuationSubring {A K : Type*} [CommRing A] [Field K]
    (f : A →+* K) (x : K) :
    f.IsIntegralElem x ↔ ∀ V : ValuationSubring K, (∀ a : A, f a ∈ V) → x ∈ V := by
  let : Algebra A K := f.toAlgebra
  change _root_.IsIntegral A x ↔ _
  -- Intersect the valuation subrings containing the integral closure. By integral closedness, a
  -- valuation subring contains that closure exactly when it contains the image of f.
  rw [← mem_integralClosure_iff, ← Subalgebra.mem_toSubring,
    Subring.eq_iInf_of_isIntegrallyClosedIn (R := (integralClosure A K).toSubring),
    Subring.mem_iInf]
  have h_image (V : ValuationSubring K) :
      (integralClosure A K).toSubring ≤ V.toSubring ↔ ∀ a : A, f a ∈ V := by
    let : IsIntegrallyClosedIn V.toSubring K := inferInstanceAs (IsIntegrallyClosedIn V K)
    exact Subring.integralClosure_le_iff
  exact ⟨fun h V hV ↦ h ⟨V, (h_image V).mpr hV⟩,
    fun h ⟨V, hV⟩ ↦ h V ((h_image V).mp hV)⟩
