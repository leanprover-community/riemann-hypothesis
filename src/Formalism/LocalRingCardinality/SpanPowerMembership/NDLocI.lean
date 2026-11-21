import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Formalism.LocalRingCardinality.SpanPowerMembership.UrPkgNonempty
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocH

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc LB


namespace TwB

section Settings

variable (F : Type) [Field F] [NumberField F]

abbrev TwT : Type :=
  Σ l : Nat.Primes, {w : HeightOneSpectrum (𝓞 F) // (((l : ℕ) : ℕ) : 𝓞 F) ∈ w.asIdeal}

instance (i : TwT F) : Fact ((i.1 : ℕ)).Prime := ⟨i.1.2⟩

def phi (i : TwT F) : F →+* PadicAlgCl (i.1 : ℕ) := (exists_embAt i.2.1 i.2.2).choose

theorem phi_spec (i : TwT F) (x : 𝓞 F) : x ∈ i.2.1.asIdeal ↔ ‖phi F i (x : F)‖ < 1 := by
  exact (exists_embAt i.2.1 i.2.2).choose_spec x

end Settings

section OneLL

variable {l : ℕ} [hl : Fact l.Prime] {F : Type} [Field F] (LL : FinExt l) (φ : F →+* PadicAlgCl l)
  (hφ : ∀ x, φ x ∈ LL.1)

def phiL : F →+* ↥LL.1 := φ.codRestrict LL.1.toSubfield hφ


def embF : F →+* FractionRing ↥(OL LL) := (toFrac LL).comp (phiL LL φ hφ)


def pkg : UrPkg l ↥(OL LL) :=
  (urPkg_nonempty l ↥(OL LL) (toC LL) (toC_injective LL)
    (fun x => (norm_toC LL x).le.trans (nrm_le LL x))
    (fun x hx => by rw [norm_toC]; exact (mem_max LL x).mp hx)).some

end OneLL

end TwB

end Formalism.BasicNotions.Examples₂
