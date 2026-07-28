import TameDelPezzo

open TameDelPezzo.CyclicQuotient

def main : IO Unit := do
  IO.println "tame-del-pezzo lean certificate"
  IO.println s!"independent pairs through order 48: {representationCount 48}"
  IO.println s!"independent implementations agree: {implementationsAgreeUpTo 48}"
  IO.println s!"primary pairs through order 256: {representationCount 256}"
  IO.println s!"primary smooth classifications: {smoothCount 256}"
  IO.println s!"primary singular classifications: {representationCount 256 - smoothCount 256}"
