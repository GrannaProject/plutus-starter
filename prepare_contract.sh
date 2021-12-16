#!/usr/bin/env bash
echo "Creating wallet..."

export WALLET_ID=`curl -s -d '' http://localhost:9080/wallet/create | jq '.wiWallet.getWalletId'`
echo "WALLET_ID=${WALLET_ID}"

echo "Activating contract instance..."
export INSTANCE_ID=`curl -s -H "Content-Type: application/json" \
  --request POST \
  --data '{"caID": "GrannaContract", "caWallet":{"getWalletId": '$WALLET_ID'}}' \
  http://localhost:9080/api/contract/activate | jq '.unContractInstanceId' | tr -d '"'`
echo "INSTANCE_ID=${INSTANCE_ID}"

MRK_STR="617364666173646661736466"
