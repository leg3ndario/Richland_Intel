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
    lists = data.get('data', [])
    for l in lists:
        # This prints every piece of info DealMachine has on the list
        print(f"RAW DATA: {l}") 
else:
    print(f"Failed: {response.text}")
