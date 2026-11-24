module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Topology

namespace GlobalTheory.CompanionTheory.RgEisTop

section Units

variable {M : Type} [TopologicalSpace M] [Monoid M] [ContinuousMul M] [T2Space M]

theorem isClosedEmbedding_embedProduct : IsClosedEmbedding (Units.embedProduct M) := by
  refine ⟨Units.isEmbedding_embedProduct, ?_⟩
  have hr : Set.range (Units.embedProduct M) =
      {p : M × Mᵐᵒᵖ | p.1 * MulOpposite.unop p.2 = 1} ∩
        {p : M × Mᵐᵒᵖ | MulOpposite.unop p.2 * p.1 = 1} := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨u, hu⟩
      have h1 : (u : M) = x := congrArg Prod.fst hu
      have h2 : MulOpposite.op ((u⁻¹ : Mˣ) : M) = y := congrArg Prod.snd hu
      subst h1 h2
      exact ⟨u.mul_inv, u.inv_mul⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, MulOpposite.unop y, h1, h2⟩, rfl⟩
  rw [hr]
  have hu : Continuous fun p : M × Mᵐᵒᵖ => MulOpposite.unop p.2 :=
    MulOpposite.continuous_unop.comp continuous_snd
  exact (isClosed_eq (continuous_fst.mul hu) continuous_const).inter
    (isClosed_eq (hu.mul continuous_fst) continuous_const)

end Units

section Mat

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  (ι : Type) [Fintype ι] [DecidableEq ι]

theorem generalLinear_t2Space [T2Space R] : T2Space (GL ι R) :=
  (isClosedEmbedding_embedProduct (M := Matrix ι ι R)).isEmbedding.t2Space

theorem gl_locallyCompact [T2Space R] [LocallyCompactSpace R] : LocallyCompactSpace (GL ι R) := by
  have : LocallyCompactSpace (Matrix ι ι R) := inferInstanceAs (LocallyCompactSpace (ι → ι → R))
  have : LocallyCompactSpace (Matrix ι ι R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix ι ι R)).symm.isClosedEmbedding.locallyCompactSpace
  exact (isClosedEmbedding_embedProduct (M := Matrix ι ι R)).locallyCompactSpace

theorem gl_secondCountable [T2Space R] [SecondCountableTopology R] :
    SecondCountableTopology (GL ι R) := by
  have : SecondCountableTopology (Matrix ι ι R) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → R))
  have : SecondCountableTopology (Matrix ι ι R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix ι ι R)).symm.isEmbedding.secondCountableTopology
  exact (isClosedEmbedding_embedProduct (M := Matrix ι ι R)).isEmbedding.secondCountableTopology

end Mat

open PositivityTheory.RgEis

theorem isClosed_uSub {E R : Type} [Field E] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] (A : Ad E R) (hσ : Continuous A.σ) (ε : ℤˣ)
    (ι : Type) [Fintype ι] [DecidableEq ι] :
    IsClosed (A.uSub ε ι : Set (GL (ι ⊕ ι) R)) := by
  have hv : Continuous fun g : GL (ι ⊕ ι) R => (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
    Units.continuous_val
  have hm : Continuous fun g : GL (ι ⊕ ι) R => (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ :=
    hv.matrix_map hσ
  exact isClosed_eq ((hv.matrix_transpose.mul continuous_const).mul hm) continuous_const

theorem grpTop : PositivityTheory.RgEis.GrpTop := by
  intro E R _ _ _ _ _ _ _ A hA ι _ _ ε
  have hc := isClosed_uSub A hA.σcont ε ι
  have hce : IsClosedEmbedding (Subtype.val : A.U ε ι → GL (ι ⊕ ι) R) :=
    hc.isClosedEmbedding_subtypeVal
  have := generalLinear_t2Space R (ι ⊕ ι)
  have := gl_locallyCompact R (ι ⊕ ι)
  have := gl_secondCountable R (ι ⊕ ι)
  refine ⟨generalLinear_t2Space R ι, gl_locallyCompact R ι, gl_secondCountable R ι, hce.isEmbedding.t2Space,
    hce.locallyCompactSpace, hce.isEmbedding.secondCountableTopology, ?_⟩
  exact hce.isCompact_preimage (hA.toGoodL.kcpt (ι ⊕ ι))

end GlobalTheory.CompanionTheory.RgEisTop
