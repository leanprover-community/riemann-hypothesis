module

public import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqOfInert
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersAgreeInertUnramified
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem unrAt_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : HeightOneSpectrum (𝓞 E)) : UnrAt (1 : Chr F E) w := fun x _ => by
  simp [locChar]

theorem charSt : CharSt := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hX v w hw hv z hz
  have h : w.under (𝓞 F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
  have hwT : w ∉ above E (X.T : Set (Pl F)) := fun hm => hv (h ▸ hm)
  have hev : Even (a' + a) := by rw [add_comm]; exact hX.geo.even
  have hres : ∀ b : (AF F)ˣ, (X.α * X.β) (ideleMap F E b) = (1 : Chr F E) (ideleMap F E b) := by
    intro b
    have hA : ((X.α (ideleMap F E b) : Circle) : ℂ) = _ := hX.chars.resα b
    have hB : ((X.β (ideleMap F E b) : Circle) : ℂ) = _ := hX.chars.resβ b
    rw [MonoidHom.mul_apply, MonoidHom.one_apply, ← Circle.coe_eq_one, Circle.coe_mul, hA, hB]
    split_ifs
    · simp
    · rw [← pow_add, hev.neg_one_pow]
  have key := GlobalTheory.InertChars.locIdele_eq_of_inert hw (X.α * X.β) 1 hres
    ((hX.chars.unrα w hwT).mul (hX.chars.unrβ w hwT)) (unrAt_one w)
  refine ⟨?_, GlobalTheory.InertChars.beta_eq_alpha_of_inert F E σ B a a' G X om om' hX v w hw hv z hz⟩
  rw [GlobalTheory.InertChars.eq_ideleAt_of_at z hz, GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw, ← MonoidHom.mul_apply, key,
    MonoidHom.one_apply]

end PositivityTheory.Sph

end
