import Development.EtaleCohomology.EtaleSheaves.LeafDescendChainPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf

namespace LateralTheory.E.LeafPropsDescendPf

def LeafSpreadOne : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → IsProper c →
    SmoothOfRelativeDimension 1 c → IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → IsProper q' ∧ SmoothOfRelativeDimension 1 q'

def LeafBaseChangePre : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R R' : Subalgebra k Ω)
    (hR : R ≤ R') {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}}
    (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
    PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2 →
    ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1) (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1)
      (w2 : C2 ⟶ E2) (r0 : E0 ⟶ D0) (r1 : E1 ⟶ D1) (r2 : E2 ⟶ D2),
      (IsPullback w0 c0 q' (toR R') ∧ IsPullback w1 (γ1 ≫ c0) (e1 ≫ q') (toR R') ∧
        IsPullback w2 (γ2 ≫ γ1 ≫ c0) (e2 ≫ e1 ≫ q') (toR R') ∧ γ1 ≫ w0 = w1 ≫ e1 ∧ γ2 ≫ w1 = w2 ≫ e2) ∧
      IsPullback r0 q' q (incl hR) ∧ IsPullback r1 (e1 ≫ q') (d1 ≫ q) (incl hR) ∧
      IsPullback r2 (e2 ≫ e1 ≫ q') (d2 ≫ d1 ≫ q) (incl hR)


end LateralTheory.E.LeafPropsDescendPf

end
