module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Formalism.LocalRingCardinality.DataNChoice
public import Formalism.LocalRingCardinality.DataNChTie
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems

variable (D : D7)

abbrev TwDatum : Type :=
  Σ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (k : ℕ), (D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ)

def Twisted (w : D.what₂.places.Pl) : Prop := D.what₂.muAt w ≠ D.what₂.mu0

def SameBelow (w w' : D.what₂.places.Pl) : Prop :=
  ∀ x : ↥D.LL0, 0 ≤ D.what₂.places.val w (x : D.what₂.LL) ↔ 0 ≤ D.what₂.places.val w' (x : D.what₂.LL)

def SamePair (w w' : D.what₂.places.Pl) : Prop :=
  SameBelow D w w' ∨ SameBelow D (D.what₂.places.conj w) w'

def LiesUnder (i : D.ntw.Tw) (w : D.what₂.places.Pl) : Prop :=
  ∀ x : 𝓞 ↥D.LL0,
    (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : ↥D.LL0)) ↔
    0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL)

variable {D}

def recorded (c : NChoice D) (w : D.what₂.places.Pl) : TwDatum D :=
  ⟨c.twI w, c.Q w, c.k' w, BlochKatoReduction.Gen.psiAt (c.sd w) (c.psi' w)⟩

open NumberField IsDedekindDomain in
variable (D : _root_.Formalism.BasicNotions.D7) in
variable {D} in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj (w : D.what₂.places.Pl) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D (D.what₂.places.conj w) ↔ _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted
  rw [_root_.Formalism.BasicNotions.Rows.Data.muAt_conj]

end GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems

end
