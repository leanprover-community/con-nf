import ConNF.FOA.Basic.Hypotheses

open ConNF

variable [Params]

class SingleDerivative (X : Type _) (Y : outParam <| Type _)
    (β : outParam TypeIndex) (γ : TypeIndex) where
  sderiv : X → γ < β → Y

class Derivative (X : Type _) (Y : outParam <| Type _)
    (β : outParam TypeIndex) (γ : TypeIndex) where
  deriv : X → Quiver.Path β γ → Y

class BotSingleDerivative (X : Type _) (Y : outParam <| Type _) where
  botSderiv : X → Y

class BotDerivative (X : Type _) (Y : outParam <| Type _) (β : outParam TypeIndex) where
  botDeriv : X → ExtendedIndex β → Y

class SingleCoderivative (X : Type _) (Y : outParam <| Type _)
    (β : TypeIndex) (γ : outParam TypeIndex) where
  scoderiv : X → γ < β → Y

class Coderivative (X : Type _) (Y : outParam <| Type _)
    (β : TypeIndex) (γ : outParam TypeIndex) where
  coderiv : X → Quiver.Path β γ → Y

infixl:75 " ↘ " => SingleDerivative.deriv
infixl:75 " ⇘ " => Derivative.deriv
postfix:75 " ↘." => BotSingleDerivative.botDeriv
infixl:75 " ⇘. " => BotDerivative.botDeriv
infixl:75 " ↗ " => SingleCoderivative.scoderiv
infixl:75 " ⇗ " => Coderivative.coderiv

@[default_instance 10]
instance (X : Type _) (Y : outParam <| Type _)
    (β : outParam TypeIndex) (γ : TypeIndex) [Derivative X Y β γ] :
    SingleDerivative X Y β γ where
  sderiv x h := x ⇘ Quiver.Hom.toPath h

@[default_instance 10]
instance (X : Type _) (Y : outParam <| Type _) (β : outParam Λ) [BotDerivative X Y β] :
    BotSingleDerivative X Y where
  botSderiv x := x ⇘. Quiver.Hom.toPath (WithBot.bot_lt_coe β)

@[default_instance 10]
instance (X : Type _) (Y : outParam <| Type _)
    (β : TypeIndex) (γ : outParam TypeIndex) [Coderivative X Y β γ] :
    SingleCoderivative X Y β γ where
  scoderiv x h := x ⇗ Quiver.Hom.toPath h
