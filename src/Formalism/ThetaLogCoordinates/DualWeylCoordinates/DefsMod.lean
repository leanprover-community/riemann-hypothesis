module

public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsObj

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma genMat_map_coord {n : ℕ} (F : Type) [CommRing F] :
    (MvPolynomial.map (Int.castRingHom F)).mapMatrix (genMat ℤ n) = genMat F n := by
  ext a b
  simp [genMat]

def mapCoord {n : ℕ} (F : Type) [CommRing F] : GLCoord ℤ n →+* GLCoord F n :=
  IsLocalization.Away.lift (genMat ℤ n).det
    (g := (algebraMap (MvPolynomial (Fin n × Fin n) F) (GLCoord F n)).comp (MvPolynomial.map (Int.castRingHom F)))
    (by rw [RingHom.comp_apply, RingHom.map_det, genMat_map_coord]
        exact IsLocalization.Away.algebraMap_isUnit _)

attribute [instance] GLMod.fi GLMod.de

def TCols {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Finset ℤ := Finset.Ioc (mu (lastIdx n)) (mu 0)

abbrev TIdx {n : ℕ} [NeZero n] (mu : Fin n → ℤ) :=
  (c : ↥(TCols mu)) → {J : Finset (Fin n) // J.card = colH mu c}

lemma colH_le {n : ℕ} (mu : Fin n → ℤ) (c : ℤ) : colH mu c ≤ n :=
  le_of_le_of_eq (Finset.card_filter_le _ _) (by simp)

def canT {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : TIdx mu :=
  fun c => ⟨(univ : Finset (Fin (colH mu c))).map (Fin.castLEEmb (colH_le mu c)), by simp⟩

def minorC {n h : ℕ} (J I : Finset (Fin n)) (hJ : J.card = h) (hI : I.card = h) : GLCoord ℤ n :=
  algebraMap _ (GLCoord ℤ n)
    (Matrix.det (Matrix.of fun a b : Fin h => genMat ℤ n (J.orderEmbOfFin hJ a) (I.orderEmbOfFin hI b)))

def detU (n : ℕ) : (GLCoord ℤ n)ˣ := (IsLocalization.Away.algebraMap_isUnit (genMat ℤ n).det).unit

def TMat {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Matrix (TIdx mu) (TIdx mu) (GLCoord ℤ n) :=
  fun J I => ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
    ∏ c : ↥(TCols mu), minorC (J c).1 (I c).1 (J c).2 (I c).2

def brk {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) : GLCoord ℤ n := TMat mu (canT mu) I

def StdT {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) : Prop :=
  ∀ (c : ↥(TCols mu)) (hc : (c : ℤ) + 1 ∈ TCols mu) (t : Fin n),
    ((I ⟨(c : ℤ) + 1, hc⟩).1.filter (· ≤ t)).card ≤ ((I c).1.filter (· ≤ t)).card

attribute [instance] ColFam.fJ ColFam.dJ

lemma genMat_map_evalR {n : ℕ} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (g : Matrix (Fin n) (Fin n) R') :
    (MvPolynomial.eval₂Hom (algebraMap R R') (fun ab : Fin n × Fin n => g ab.1 ab.2)).mapMatrix (genMat R n) = g := by
  ext a b
  simp [genMat]

def evGLR {n : ℕ} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (g : GL (Fin n) R') : GLCoord R n →+* R' :=
  IsLocalization.Away.lift (genMat R n).det
    (g := MvPolynomial.eval₂Hom (algebraMap R R') (fun ab : Fin n × Fin n => g.val ab.1 ab.2))
    (by rw [RingHom.map_det, genMat_map_evalR]; exact Matrix.isUnits_det_units g)

def inducedSections {n : ℕ} (R : Type) [CommRing R] (mu : Fin n → ℤ) : Set (GLCoord R n) :=
  {f | ∀ (R' : Type) [CommRing R'] [Algebra R R'] (b g : GL (Fin n) R'), (∀ a c : Fin n, a < c → b.val a c = 0) →
    evGLR (b * g) f * ∏ a, b.val a a ^ (-(mu a)).toNat = (∏ a, b.val a a ^ (mu a).toNat) * evGLR g f}

def rowLetters (n : ℕ) : Letters (Fin n) := ⟨fun _ => true⟩

def brkPol {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) : MvPolynomial (Fin n × Fin n) ℤ :=
  (genMat ℤ n).det ^ (mu (lastIdx n)).toNat *
    ∏ c : ↥(TCols mu), Matrix.det (Matrix.of fun a b : Fin (colH mu c) =>
      genMat ℤ n ((canT mu c).1.orderEmbOfFin (canT mu c).2 a) ((I c).1.orderEmbOfFin (I c).2 b))

end Formalism.InvariantFactorPaths.ColumnFamilies
