import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.CharIdem

section

variable {G : Type} [Group G]

open Classical in

noncomputable def charFn (K : Subgroup G) (χ : K →* Circle) (c : ℝ) : G → ℂ :=
  fun x => if h : x ∈ K then star ((χ ⟨x, h⟩ : Circle) : ℂ) / (c : ℂ) else 0

variable (K : Subgroup G) (χ : K →* Circle) (c : ℝ)


variable [TopologicalSpace G] [IsTopologicalGroup G]

variable [MeasurableSpace G] [BorelSpace G]

end

end GlobalTheory.CharIdem
