import requests
import os

API_KEY = os.getenv('DEALMACHINE_API_KEY')
URL = "https://api.dealmachine.com/public/v1/lists/"

headers = {
    "Authorization": f"Bearer {API_KEY}",
    "Content-Type": "application/json"
}

response = requests.get(URL, headers=headers)
data = response.json()

if response.status_code == 200:
    print("\n--- YOUR DEALMACHINE LISTS ---")
    # DealMachine usually returns a list of objects in the 'data' key
    lists = data.get('data', [])
    if not lists:
        print("No lists found. Create one in the DealMachine UI first!")
    for l in lists:
        print(f"ID: {l.get('id')} | Name: {l.get('name')}")
    print("------------------------------\n")
else:
    print(f"Failed to fetch lists: {response.text}")
