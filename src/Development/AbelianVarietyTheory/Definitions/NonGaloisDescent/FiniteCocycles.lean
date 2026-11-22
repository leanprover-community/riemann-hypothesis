module

public import Mathlib

@[expose] public section

noncomputable section

open TensorProduct Polynomial IsLocalRing

namespace GlobalTheory.Pat

namespace Det

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

end Det

namespace GDet

variable {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)

variable [TopologicalSpace G]

end GDet

end GlobalTheory.Pat

noncomputable section

open IsLocalRing

namespace GlobalTheory.Pat

attribute [instance] PG.grp PG.top PG.tgrp PG.cpt PG.t2 PG.td

attribute [instance] Frame.hl Frame.iO Frame.iOd Frame.iOv Frame.iVl Frame.iSt

namespace Frame
variable (Φ : Frame)

end Frame

section Elements
variable {Φ : Frame} (G : PolGp Φ) {B : Type} [CommRing B]

end Elements

attribute [instance] Pair.iB Pair.iL

namespace Pair
variable {Φ : Frame} {G : PolGp Φ} (R : Pair G)

end Pair

section CH
variable {n : ℕ} {Γ B : Type} [Group Γ] [CommRing B] (D : DetG n Γ B)

end CH

namespace Pair
variable {Φ : Frame} {G : PolGp Φ} (R : Pair G)

end Pair

end GlobalTheory.Pat

noncomputable section

open IsLocalRing Polynomial

namespace GlobalTheory.Pat.Example

end GlobalTheory.Pat.Example
