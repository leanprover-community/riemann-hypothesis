module

public import Development.EtaleCohomology.TateTwists.EtaleSheafInjectiveResolutionInitialShortComplex
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ExactLocPf

variable {R : Type} [CommRing R]

lemma kernel_lift_sec (S : ShortComplex (Shv R)) (U : Scheme.{0}) (b : Sec S.X₂ U)
    (hb : Sec.map S.g b = 0) : ∃ k : Sec (kernel S.g) U, Sec.map (kernel.ι S.g) k = b := by
  let T : ShortComplex (Shv R) := ShortComplex.mk (kernel.ι S.g) S.g (kernel.condition _)
  have hT : T.Exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel S.g)
  have : Mono T.f := by dsimp [T]; infer_instance
  have hE : (T.map (LateralTheory.EtaleFoundations.ResSecPf.secF R U)).Exact :=
    hT.map_of_mono_of_preservesKernel _ this inferInstance
  rw [ShortComplex.moduleCat_exact_iff] at hE
  exact hE b hb

lemma epi_lift (S : ShortComplex (Shv R)) (hS : S.Exact) :
    Epi (kernel.lift S.g S.f S.zero) := by
  exact hS.epi_kernelLift

end LateralTheory.EtaleFoundations.ExactLocPf

open LateralTheory.EtaleFoundations.ExactLocPf in
theorem LateralTheory.EtaleFoundations.ResSecPf.exact_loc_of : LateralTheory.EtaleFoundations.ResSecPf.exact_loc := by
  intro R _ S hS U b hb
  obtain ⟨k, hk⟩ := kernel_lift_sec S U b hb
  let p := kernel.lift S.g S.f S.zero
  have : Epi p := epi_lift S hS
  have hls : Sheaf.IsLocallySurjective p := (Sheaf.isLocallySurjective_iff_epi' (φ := p)).2 this
  refine ⟨Presheaf.imageSieve p.hom k, Presheaf.imageSieve_mem Scheme.etaleTopology p.hom (U := op U) k, ?_⟩
  rintro V g ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have e1 : S.f = p ≫ kernel.ι S.g := (kernel.lift_ι _ _ _).symm
  have e2 : Sec.map S.f a = Sec.map (kernel.ι S.g) (Sec.map p a) := by
    rw [e1]; rfl
  rw [e2, ← hk]
  change Sec.map (kernel.ι S.g) ((p.hom.app _).hom a) = _
  have ha' : (p.hom.app (op V)).hom a = ((kernel S.g).obj.map g.op).hom k := ha
  rw [ha']
  exact congrArg (fun f => f.hom k) ((kernel.ι S.g).hom.naturality g.op)
