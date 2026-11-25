module

public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

section Lattice

variable {D : D7}

def StabLat (V : HSp D) (κ : GA D V) : Prop :=
  κ ∈ GfC V ∧ gLat V κ = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E))

def LevAgrees (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (M : ℕ) (Mh : Ideal (𝓞 D.host.E)) (κ : GA D V)
    (lev : La →ₗ[𝓞 D.host.E] La) : Prop :=
  ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
    finVec V (ι (lev a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = M • w

end Lattice

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

end Frames

section Statement

variable {D : D7} (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ)


include hT hj hσ in
theorem dict_mem_dom (h : GA D (T.V j σ)) : (T.dict j σ h).2 ∈ ((T.U j σ).X (T.dict j σ h).1).dom := by
  obtain ⟨_, _, _, hd⟩ := hT.dictU j hj σ hσ
  exact hd.2.2.2.1 h


end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix
