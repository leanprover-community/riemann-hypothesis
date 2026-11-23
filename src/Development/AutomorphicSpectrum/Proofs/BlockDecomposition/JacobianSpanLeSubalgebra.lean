module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cone

theorem jacSpan_le_jacS : ∀ {K : Type} [Field K] {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) [Algebra K Γ(X, V)]
    (B : Subalgebra K Γ(X, V)), (B : Set Γ(X, V)) = Set.range (rs h) →
    ∀ {d m : ℕ} (D : Fin d → Derivation K Γ(X, V) Γ(X, V)) (κ : Fin m → Fin d),
    jacSpan h (RingHom.id _) (fun k => D k) κ ≤ jacS B D κ := by
  intro K _ X V W h _ B hB d m D κ
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨b, bs, rfl⟩
  have hm : ∀ c : Γ(X, W), rs h c ∈ B := fun c => by
    have : rs h c ∈ (B : Set Γ(X, V)) := hB ▸ Set.mem_range_self c
    exact this
  exact AddSubgroup.subset_closure ⟨⟨rs h b, hm b⟩, fun l => ⟨rs h (bs l), hm (bs l)⟩, rfl⟩

end GlobalTheory.CompanionTheory.Cone
