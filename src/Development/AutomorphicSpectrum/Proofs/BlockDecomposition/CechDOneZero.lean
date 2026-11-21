import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeCech

variable {R : Type} [CommRing R] {D : Type 1} [Category.{0} D] (A : D ⥤ CommAlgCat.{0} R)

abbrev Co (k : ℕ) : Type 1 := CH.Cn (CH.modF A) k

def one0 : Co A 0 := fun s => (1 : A.obj (s.obj (Fin.last 0)))

def aL : ∀ {p : ℕ}, (Fin (p + 1) → Co A 1) → Co A p := fun {p} =>
  Nat.rec (motive := fun p => (Fin (p + 1) → Co A 1) → Co A p) (fun _ => one0 A)
    (fun p ih β => (CH.mulP A).cupC (by omega : 1 + p = p + 1) (β 0 - β 1) (ih fun i => β i.succ)) p




theorem cech_d_one_zero : CH.d (CH.modF A) 0 (one0 A) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (GlobalTheory.CatH.toLast i s)).hom 1 = (0 : A.obj _)
  rw [Fin.sum_univ_two, map_one, map_one]
  simp


theorem pow_closed (z : Co A 2) (hz : CH.d _ 2 z = 0) (k : ℕ) : CH.d _ (2 * k) (cupPowC A z k) = 0 := by
  induction k with
  | zero => exact cech_d_one_zero A
  | succ k ih =>
    have e : cupPowC A z (k + 1) = (CH.mulP A).cupC (by omega) (cupPowC A z k) z := rfl
    rw [e, P.leibniz, ih, hz]
    simp



def fP (z : Co A 2) {p : ℕ} (β : Fin (p + 1) → Co A 1) (k q : ℕ) (h : 2 * k + (p + 1) = q) : Co A q :=
  (CH.mulP A).cupC h (cupPowC A z k) ((CH.mulP A).cupC (by omega : 1 + p = p + 1) (β 0) (aL A β))

def gP (z : Co A 2) {p : ℕ} (β : Fin (p + 1) → Co A 1) (k q : ℕ) (h : 2 * k + p = q) : Co A q :=
  (CH.mulP A).cupC h (cupPowC A z k) (aL A β)



section Res

variable {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) {U V : ObjectProperty C}

def resM (h : V ≤ U) : CH.Mor (CH.modF (U.ι ⋙ A)) (CH.modF (V.ι ⋙ A)) (RingHom.id R) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem d_resB (h : V ≤ U) {k : ℕ} (b : CH.Cn (CH.modF (U.ι ⋙ A)) k) :
    CH.d _ k (resB A h b) = resB A h (CH.d _ k b) := (resM A h).d_pullC k b


theorem resB_sub (h : V ≤ U) {k : ℕ} (a b : CH.Cn (CH.modF (U.ι ⋙ A)) k) :
    resB A h (a - b) = resB A h a - resB A h b := rfl




theorem resB_resB {T : ObjectProperty C} (h : V ≤ U) (h' : T ≤ V) (h'' : T ≤ U) {k : ℕ} (b : CH.Cn (CH.modF (U.ι ⋙ A)) k) :
    resB A h' (resB A h b) = resB A h'' b := rfl

end Res

end GlobalTheory.CompanionTheory.ConeCech
