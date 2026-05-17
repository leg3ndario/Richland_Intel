import csv
import requests
import os
import time
import re

# Configuration
API_KEY = os.getenv('DEALMACHINE_API_KEY')
CSV_FILE = 'data/leads_ghl_export.csv' 
BASE_URL = "https://api.dealmachine.com/public/v1/leads/" # Added trailing slash
LIST_ID = 1254885 

def clean_address(addr):
    addr = re.sub(r'\(.*?\)', '', addr)
    addr = re.sub(r'\bUNIT\b', '#', addr, flags=re.IGNORECASE)
    return addr.strip().strip(',')

def upload_leads():
    if not API_KEY:
        print("❌ Error: DEALMACHINE_API_KEY environment variable is empty.")
        return

    if not os.path.exists(CSV_FILE):
        print(f"❌ Error: {CSV_FILE} not found.")
        return

    headers = {
        "Authorization": f"Bearer {API_KEY}",
        "Content-Type": "application/json",
        "Accept": "application/json"
    }

    with open(CSV_FILE, mode='r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        
        for row in reader:
            raw_addr = row.get('Property Address', '').strip()
            
            # Basic junk filtering
            if not raw_addr or not raw_addr[0].isdigit() or len(raw_addr) > 120:
                continue

            addr = clean_address(raw_addr)
            city = row.get('Property City', 'Columbia').strip()
            zip_code = row.get('Property Zip', '').strip()
            
            payload = {
                "address": addr,
                "city": city,
                "state": "SC",
                "zip": zip_code,
                "skip_trace": True,
                "lists": [LIST_ID]
            }

            try:
                # 1. ATTEMPT TO CREATE (POST)
                response = requests.post(BASE_URL, json=payload, headers=headers)
                res_data = response.json()
                
                lead_id = res_data.get('data', {}).get('id') if isinstance(res_data.get('data'), dict) else None
                error_msg = res_data.get('error', {}).get('message', '') if isinstance(res_data.get('error'), dict) else str(res_data.get('error'))

                if response.status_code in [200, 201] and lead_id:
                    print(f"✅ Added: {addr}")
                
                elif "already added" in error_msg.lower() or response.status_code == 200:
                    # 2. ALREADY EXISTS? FETCH THE ID AND UPDATE (PUT)
                    # Use the ID from the response or look for it
                    existing_id = res_data.get('data', {}).get('id')
                    
                    if existing_id:
                        # Constructing the PUT URL with a trailing slash
                        update_url = f"{BASE_URL}{existing_id}/"
                        update_payload = {"lists": [LIST_ID]}
                        
                        update_res = requests.put(update_url, json=update_payload, headers=headers)
                        
                        if update_res.status_code == 200:
                            print(f"🔄 Updated: {addr} (Moved to List {LIST_ID})")
                        else:
                            print(f"⚠️ Found but couldn't update: {addr} | {update_res.text}")
                    else:
                        print(f"➖ Skipped: {addr} (Already in DM, No ID returned)")
                
                else:
                    print(f"❌ Failed: {addr} | {error_msg}")
            
            except Exception as e:
                print(f"⚠️ Error: {addr} | {str(e)}")

            time.sleep(0.4)

if __name__ == "__main__":
    upload_leads()
