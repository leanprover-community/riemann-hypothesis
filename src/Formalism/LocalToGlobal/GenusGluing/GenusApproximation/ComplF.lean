module

public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]

def eP (P : HeightOneSpectrum (𝓞 F) → Prop) : E ⊗[F] Formalism.L2.Herm.Af F :=
  (1 : E) ⊗ₜ[F] ((Formalism.L2.DIV.idemAd P : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F)

def eAt (v : HeightOneSpectrum (𝓞 F)) : E ⊗[F] Formalism.L2.Herm.Af F := eP E (fun w => w = v)

def complF (v : HeightOneSpectrum (𝓞 F)) : Submonoid (𝓞 E) :=
  v.asIdeal.primeCompl.map (algebraMap (𝓞 F) (𝓞 E))

variable {E}

def locF {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) W) :
    Submodule (𝓞 E) W :=
  Formalism.HermitianLatticesTheory.locS (complF E v) L

def IntAt {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Prop :=
  ∀ i j, eAt E v * y i j ∈ Formalism.L2.Herm.intAf F E

end Formalism.L2.GenusGluing.Gen
