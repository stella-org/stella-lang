-- | The tests over inputs as deep and as long as stack safety is tested at:
-- | each is the counterpart of one the usual suite runs at a size every
-- | change affords. The Stress workflow runs them on main, nightly, and by hand.
-- | Run with `spago test -p cli -m Test.Stella.CLI.Stress`.
module Test.Stella.CLI.Stress where

import Prelude

import Effect (Effect)
import Test.Spec (describe)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Stella.CLI.Session.BrokerCodec as BrokerCodec
import Test.Stella.CLI.Session.Value as SessionValue

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  describe "Stella.CLI.Session.Value, beyond the host's call stack and its serializer" do
    SessionValue.atSize 100000
  describe "Stella.CLI.Session.Broker.Codec, a value as deep as it is, beyond the host's call stack" do
    BrokerCodec.atSize 100000
