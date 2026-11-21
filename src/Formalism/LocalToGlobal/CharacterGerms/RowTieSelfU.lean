import Formalism.LocalToGlobal.CharacterGerms.RowTieCharS

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def EnoughCharactersSelfUnramified : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))) →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : LabS E C Orb d) (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o, CHCharSelfSt Y (selfOfLab ha hg o)

def CharacterHypothesisSelfUnramified : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))) →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : LabS E C Orb d) (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o (Hc : ∀ g, (Y.rawSelf (selfOfLab ha hg o)).CartHyp V g), RawChart.CHSt Hc

variable {Xo c}
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]


end Formalism.L2.FormalSeriesBounds
