import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETExSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPointStatement

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

structure EtFactor (E : Type) [Field E] [NumberField E] (cj : E → E) where
  V : Type
  [cr : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  ϖ : V
  hϖ : Irreducible ϖ
  D : DegData V (maximalIdeal V)
  [modX : Module (𝓞 E) D.toPre.X]
  Q : D.toPre.X → ℤ
  hQ : QForm.IsQ D.toPre ϖ Q
  β : SymB cj D.toPre.X
  hβQ : ∀ a b, (β : D.toPre.X →ₗ[ℤ] D.toPre.X →ₗ[ℤ] ℝ) a b = QForm.bOf D.toPre Q a b
  hβ2 : ∀ a, (β : D.toPre.X →ₗ[ℤ] D.toPre.X →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)
  hβpos : ∀ a, 0 ≤ (β : D.toPre.X →ₗ[ℤ] D.toPre.X →ₗ[ℤ] ℝ) a a
  F : Type
  [fF : Field F]
  [aF : Algebra (FractionRing V) F]
  v : AddValuation F (WithTop ℚ)
  hv : ValOver ϖ F v
  R' : ℕ
  R₀ : ℕ
  hR' : 2 ≤ R'
  hR₀ : 2 ≤ R₀
  hdvd : R₀ ∣ R'
  r : ℕ
  y : Fin r → D.toPre.X
  hgen : ∀ a : D.toPre.X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : D.toPre.X, a = u + R₀ • t
  s : Fin r → Fam D.toPre F (R' ^ 2)
  w : Fin r → F
  hsupp : ∀ b (α : D.toPre.X), (∀ z : D.toPre.X, α ≠ y b + R' • z) → ∀ j, ((s b).s α).f j = 0
  hnu : ∀ b, NuGe D Q F v (R' ^ 2) (s b) 0
  hval : ∀ b, ValAt0 D F v (R' ^ 2) (s b) (w b)

attribute [instance] EtFactor.cr EtFactor.dom EtFactor.dvr EtFactor.modX EtFactor.fF EtFactor.aF

def wtE : WithTop ℚ → EReal
  | ⊤ => ⊤
  | (q : ℚ) => ((q : ℝ) : EReal)

namespace EtFactor

variable {E : Type} [Field E] [NumberField E] {cj : E → E}

def sumV (f : EtFactor E cj) : EReal := wtE (∑ b, f.v (f.w b))

def phiF (f : EtFactor E cj) : ℝ := phiC cj f.β / (f.R' ^ 2 : ℝ)

end EtFactor



section Link

variable {D : Formalism.BasicNotions.D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def EtFormAtSt (E : Type) [Field E] [NumberField E] (cj : E → E) (X : WeightAlgebra.PJ D B P j) (i : ℕ)
    (η : B.Cusp j (WeightAlgebra.wscalar D j (WeightAlgebra.g0 D * i) (by unfold WeightAlgebra.g0; exact ⟨5 ^ 4 * D.R.r * i, by ring⟩))) : Prop :=
  ∀ la (y : X.Pt la), ∃ (N : ℕ) (fac : Fin N → EtFactor E cj) (κ : ℝ), 0 ≤ κ ∧
    (κ : EReal) * ∑ k, (fac k).sumV ≤ X.vAt la y (X.inc _ η) ∧
    2 * i * X.phiC la y ≤ κ * ∑ k, (fac k).phiF


end Link

end Formalism.MainNotions.ModuliIntegralCharts.H1
